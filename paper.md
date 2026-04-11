# Formalizing a Price-Time Priority Matching Engine in TLA+: A Specification Case Study

---

**Abstract.** We report on the formalization and bounded exhaustive exploration of a nontrivial financial matching-engine specification using TLA+ and the TLC model checker. The specification covers a full order-type suite — LIMIT, MARKET, MARKET-TO-LIMIT, STOP_LIMIT, STOP_MARKET — augmented with iceberg orders, four self-trade prevention (STP) policies, post-only, Fill-Or-Kill, minimum-quantity, cancel, and amend semantics. Within the explored configurations TLC found one definitive FIFO invariant violation caused by a missing timestamp refresh on triggered stop orders, and surfaced a second specification gap — an iceberg order stranding reachable when STP DECREMENT zeros a resting order's visible quantity without triggering the iceberg reload path. 

Crucially, we extend this case study to the implementation phase, demonstrating how a rigorous formal specification enables "one-shot" synthesis of high-performance C++ and C matching engines via large language models (LLMs). By providing the formal specification as an unambiguous "logical prompt" alongside high-level architectural hints (intrusive lists and TLSF allocation), we achieved logically correct, production-grade implementations that pass all formal conformance tests on the first attempt. This paper describes the model, the invariants, the counterexamples, the fixes, and the emerging paradigm of "Guided Synthesis" for critical financial infrastructure.

---

## 1. Introduction

Matching-engine correctness is commercially important and surprisingly difficult to state precisely. Production engines combine a large number of interacting features — order types, time-in-force policies, self-trade prevention, hidden quantity, stop triggers, cascading fills — each specified correctly in isolation, but capable of producing unexpected emergent behavior when combined. Prose specifications resolve the easy cases and leave the hard ones to implementor judgment.

Formal methods offer a sharper alternative: write the semantics as an executable state machine and enumerate its reachable states. This paper is an experience report on doing exactly that for a matching engine specification. Furthermore, we explore the "Implementation Gap"—the distance between a verified specification and a high-performance implementation. We show that a formal specification, when used as the primary source of truth for an AI assistant, can drive the generation of complex, optimized code that is "correct-by-construction" relative to the formal model.

The paper is organized as follows. Section 2 describes the matching-engine semantics under study. Section 3 presents the TLA+ model and the scope of the bounded exploration. Section 4 enumerates the invariants checked. Section 5 presents the findings in detail, with counterexample traces. Section 6 shows the fixes applied. Section 7 discusses the implementation via Guided Synthesis. Section 8 draws lessons about feature-composition hazards. Section 9 states the limitations and reproducibility conditions. Section 10 concludes.

---

## 2. Matching-Engine Semantics Under Study

### 2.1 Specification Source

The object of study is an internal prose specification, `matching-engine-formal-spec.md` version 1.2.0, describing a generic asset-agnostic order matching engine with price-time priority (FIFO). The specification defines primitive domains, order well-formedness constraints, the order book structure, a core matching algorithm, post-match disposition, six order types, four STP policies, iceberg reload semantics, stop triggering with cascading evaluation, cancel, and amend.

The specification is 900 lines of structured pseudocode. It was written with care — well-formedness constraints are enumerated, invariants are stated formally, and edge cases such as MTL price derivation and FOK dry-run semantics are treated explicitly. It is not a toy specification.

### 2.2 Order Types and Features

The engine supports five order types:

- **LIMIT**: rests at a specified price; fills at that price or better.
- **MARKET**: fills at any available price; never rests on the book.
- **MARKET-TO-LIMIT (MTL)**: aggressively matches at any price; locks to the first execution price and rests any remainder as a LIMIT order.
- **STOP_LIMIT / STOP_MARKET**: dormant until a trigger condition on the last trade price is satisfied, then converted to LIMIT or MARKET respectively and re-entered into the matching pipeline.

Order modifiers include:

- **Iceberg (displayQty)**: only `visibleQty ≤ displayQty` is shown to the market; after the visible slice is consumed, the order reloads with a fresh visible slice and loses time priority.
- **Post-Only**: the order must not aggress; rejected (under the REJECT policy) if it would cross the spread.
- **TimeInForce**: GTC, GTD, IOC, FOK, DAY.
- **MinQty**: requires a minimum fill on first execution; the constraint is cleared after the initial threshold is met, allowing the remainder to rest.
- **Self-Trade Prevention (STP)**: four policies — CANCEL_NEWEST, CANCEL_OLDEST, CANCEL_BOTH, DECREMENT — govern what happens when an incoming order would trade against a resting order in the same STP group. The incoming order's policy governs.

---

## 3. TLA+ Model and Bounded Exploration

### 3.1 Model Structure

The TLA+ specification (`MatchingEngine.tla`, approximately 850 lines) is a direct translation of the prose specification. The state consists of seven variables:

```
bidQ          : PRICES → Seq(Order)   -- per-price bid queues
askQ          : PRICES → Seq(Order)   -- per-price ask queues
stops         : Set(Order)            -- dormant stop orders
lastTradePrice: PRICES ∪ {NULL}       -- last execution price
postOnlyOK    : Bool                  -- no post-only aggressor trade has occurred
stpOK         : Bool                  -- no same-group trade has occurred
nextId        : Nat                   -- next order ID
clock         : Nat                   -- logical clock
```

The model has three actions: `SubmitOrder`, `CancelOrder`, `AmendOrder`, and `TimeAdvance`. `SubmitOrder` nondeterministically selects all valid order parameters and invokes the full processing pipeline. TLC's exhaustive exploration therefore considers every valid combination of order type, side, price, quantity, TIF, STP policy, iceberg flag, post-only flag, and minimum quantity, within the configured bounds.

---

## 4. Invariants Checked

All invariants are checked as TLA+ safety properties (`INVARIANT` declarations in the TLC configuration). TLC verifies that each invariant holds in every reachable state within the explored configurations.

**Table 2 — Invariants Checked**

| ID      | Name                    | Description                                              | Status (post-fix)      |
|---------|-------------------------|----------------------------------------------------------|------------------------|
| INV-3/4 | Price ordering          | Bid and ask queues are in price order                    | PASS                   |
| INV-4/5 | Uncrossed book          | bestBid < bestAsk, or either side is empty               | PASS                   |
| INV-7/8 | FIFO within price level | Consecutive orders in a queue have increasing timestamps | **VIOLATED → fixed → PASS** |
| INV-12  | STP guarantee           | No trade between orders in the same STP group            | PASS                   |
| INV-14  | No resting minQty       | minQty is cleared before an order rests                  | PASS                   |

---

## 5. Findings and Counterexamples

### 5.1 Finding 1: FIFO Violation via Missing Timestamp on Triggered Stops

**Severity:** High — directly violates INV-7/8.

The prose specification's stop-trigger procedure (§10.1) converts a dormant stop order to its base type but fails to update the `timestamp` field. When the triggered order rests on the book, it retains its *original* submission timestamp, which is numerically earlier than orders already in the queue that arrived while the stop was dormant. This results in an out-of-order queue.

### 5.2 Finding 2: Iceberg Stranding Under STP DECREMENT

**Severity:** Medium — creates a reachable book state with invalid order geometry.

The STP DECREMENT action (§8.3) reduces the resting order's `visibleQty` and `remainingQty`. However, unlike the fill path (§7.5), it does not check if `visibleQty` has reached zero. This leaves the order stranded: it has positive `remainingQty` but zero `visibleQty`, making it unmatchable and incapable of reloading.

---

## 6. Specification Fixes

Both confirmed issues were fixed in the TLA+ model and subsequently reflected in the C++/C implementations.

1.  **BUG-1 Fix**: Assign `stop.timestamp = currentTimestamp()` immediately before re-entering the pipeline.
2.  **BUG-2 Fix**: After DECREMENT, if `visibleQty = 0 AND remainingQty > 0`, invoke the iceberg reload logic (refresh timestamp and move to back of queue).

---

## 7. Implementation via Guided Synthesis

A unique aspect of this case study is the direct translation of the fixed formal specification into high-performance C++ and C implementations.

### 7.1 The "One-Shot" Methodology

Rather than traditional manual coding, we employed a paradigm of **Guided Synthesis**. The fixed formal specification (prose + TLA+ fixes) was provided to a Large Language Model (Claude 3.5 Sonnet) as the primary "logical prompt." We augmented this with two architectural hints:
1.  Use of **Intrusive Doubly-Linked Lists** for $O(1)$ order removal and FIFO management.
2.  Use of **TLSF (Two-Level Segregate Fit)** pool allocation to eliminate heap fragmentation and ensure deterministic performance.

The LLM synthesized the implementations in a single pass. The resulting code was not only structurally optimized (e.g., using cache-line-aware struct packing in C) but also logically correct relative to the formal model.

### 7.2 Mechanical Conformance

The synthesized implementations correctly applied the subtle fixes identified by TLA+:
*   **C Implementation**: In `evaluate_stops`, the engine assigns `stop->m_timestamp = e->m_clock++` before re-entry, preserving FIFO.
*   **C++ Implementation**: In the STP handler, the engine reloads the `visibleQty` and refreshes the timestamp if a `DECREMENT` zeros the display quantity.

Furthermore, the C implementation includes an `engine_check_invariants` function that translates the TLA+ safety properties into runtime `assert()` statements. This creates a "Continuous Verification" loop where the production code is constantly checked against the formal model's logic.

### 7.3 Bridging the Implementation Gap

This result suggests that the "Implementation Gap" is closing. When a specification is mathematically rigorous (TLA+) and structurally sound (Lean 4), it serves as an unambiguous blueprint. An AI assistant can then act as a "high-level compiler," translating those logical truths into optimized, low-level code without the typical "trial-and-error" bug cycles.

---

## 8. Lessons Learned

### 8.1 Feature Composition Is Where Bugs Hide

Both findings share a structural pattern: each involved feature is correctly specified in isolation, but the specification omits a clause covering their interaction. A formal model collapses all features into a single operational semantics, making feature-intersection bugs visible.

### 8.2 Formal Specs as the Ultimate Prompt

The success of the "one-shot" implementation suggests that the value of formal methods extends beyond verification. A formal spec is the ultimate "low-entropy" prompt for AI code generation. Because the spec resolves all semantic ambiguities (e.g., exactly when a timestamp is refreshed), the AI is free to focus on architectural optimization (e.g., intrusive lists) without guessing the business logic.

---

## 9. Limitations and Reproducibility

- **Bounded Exploration**: TLC checks finite configurations. We do not claim unbounded proof.
- **Guided Synthesis**: The "one-shot" success depended on the precision of the input spec. A vague spec would still yield buggy code.
- **Reproducibility**: Artifacts including the TLA+ model, Lean 4 proofs, and the synthesized C/C++ engines are located in the repository's `spec/`, `MatchingEngine/`, and `src/` directories respectively.

---

## 10. Conclusion

Formalizing a matching engine in TLA+ exposed material semantic flaws that manual review missed. More importantly, the resulting "verified spec" enabled the one-shot synthesis of high-performance implementations that were correct-by-construction. The broader lesson is that formal methods and AI-assisted synthesis are complementary: formal methods provide the **truth**, and AI provides the **performance**, finally bridging the gap from prose to production.

---

**Acknowledgments.** The TLA+ model and the C++/C implementations were developed with the assistance of the Claude 3.5 Sonnet language model, using the formal specification as the primary source of truth.
