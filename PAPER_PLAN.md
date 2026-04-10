# Paper Plan: TLA+ Case Study for a Matching Engine

## Recommended framing

Write this as a short, rigorous case-study paper or experience report.

The paper should make one central claim:

Formalizing a feature-rich price-time-priority matching engine in TLA+ exposed subtle semantic bugs and edge-case interactions that were not obvious from the prose specification alone.

This is a strong and credible claim. Do not position it as a grand theory paper, and do not claim general correctness of all matching engines or all order-routing semantics.

## What the paper is actually about

The paper is about verification of a formal specification, not verification of a production implementation.

That distinction must stay explicit throughout:

- The artifact under study is the prose spec plus its TLA+ formalization.
- The main result is that model checking exposed problems in the specification.
- The contribution is not "we proved the matcher correct."
- The contribution is "we formalized a nontrivial matcher specification, checked meaningful invariants, found concrete bugs, and derived precise spec repairs."

## Main thesis

The most interesting technical point is not the existence of FIFO matching by itself. It is that the composition of advanced order semantics creates non-obvious bugs:

- stop triggering interacts with queue priority,
- self-trade prevention interacts with iceberg visibility,
- minimum quantity and FOK semantics interact with decrement behavior,
- and these interactions are hard to reason about reliably in prose.

That is the narrative spine of the paper.

## Primary contributions to claim

Claim only contributions the current artifacts can support:

1. A formal TLA+ model of a feature-rich price-time-priority matching engine.
2. A clear invariant suite covering book consistency, queue fairness, and order-type safety conditions.
3. Discovery of at least one concrete specification bug via TLC counterexample.
4. Identification of additional specification gaps or fragile semantic interactions.
5. Minimal, precise amendments to the specification.

## Strongest result

The flagship result should be the stop-trigger timestamp bug.

Why this should lead the paper:

- It is high severity.
- It directly violates FIFO within a price level.
- It has a clean, understandable counterexample.
- It demonstrates the exact kind of bug formal methods are good at finding.

Use the report's counterexample as the central motivating example:

- a stop order is submitted and held off-book,
- another order trades and triggers it,
- the triggered stop enters the matching pipeline,
- the triggered order is appended behind a later order in the queue,
- but keeps an earlier timestamp,
- producing a FIFO inconsistency.

This is the paper's best evidence that the work matters.

## Secondary result

The STP DECREMENT plus iceberg issue is useful, but the wording must be careful.

If the available artifacts do not include a preserved TLC failing trace on the unfixed model, describe it as:

"a formalization-discovered specification hole"

or

"a semantic bug revealed during formalization and model construction"

rather than strongly claiming a standalone counterexample result unless you can show it directly.

The paper can still explain why it is serious:

- a resting iceberg may become invisible with remaining quantity still positive,
- the spec provides no reload path after DECREMENT,
- this can strand quantity and induce invalid zero-quantity match behavior or looping.

## Additional observations

The FOK/minQty observations should not be treated as headline bugs unless they are backed by explicit failing traces.

Instead, frame them as semantic edge cases or underspecified interactions:

- FOK can be "fully consumed" by a mix of decrement and trades, which may differ from some readers' intuitive meaning of fill-or-kill.
- minQty may fail to guarantee actual traded quantity >= minQty when STP DECREMENT is involved.
- clearing minQty in multiple pipeline phases is correct but structurally fragile.

These observations improve the paper because they show the model was useful beyond a single bug hunt.

## Scope statement Claude should preserve

The paper should explicitly say:

- The checking is bounded model checking with TLC.
- Exhaustiveness applies only within the selected finite configurations.
- The paper studies safety and semantic consistency, not throughput, latency, market microstructure realism, or regulatory compliance.
- The paper does not claim correspondence to any particular exchange rulebook unless such mapping is added later.

This is important for credibility.

## Suggested target venues and format

Best fit:

- workshop paper,
- experience report,
- formal methods in practice track,
- systems verification case-study venue,
- or a polished technical report / arXiv note.

Do not optimize the draft for a top-tier novelty bar unless you substantially broaden it with:

- comparison to prior exchange specifications,
- multiple bug classes across implementations,
- or a reusable verification methodology with broader claims.

## Proposed paper structure

### 1. Introduction

Goal:
Explain why matching engines are difficult to specify once advanced order semantics are included.

What this section should do:

- Briefly introduce price-time-priority matching.
- Explain that seemingly local features such as stops, STP, iceberg reload, and minQty interact in non-local ways.
- State that the prose specification was formalized in TLA+ and checked with TLC.
- Preview the main result: a triggered stop order can violate FIFO if its timestamp is not refreshed.
- Preview the second result: STP DECREMENT exposes an iceberg visibility hole.

End with a short contributions list.

### 2. Semantics of the Matching Engine

Goal:
Give readers enough semantics to understand the findings without drowning them in operational detail.

Cover:

- price-time matching loop,
- passive-price execution rule,
- time-in-force behavior,
- stop orders,
- iceberg reload,
- STP policies,
- market-to-limit conversion,
- minQty semantics.

This section should lean on the prose spec, but compress it into a readable system model.

### 3. Formalization in TLA+

Goal:
Explain the model structure and what was abstracted.

Include:

- state variables and book representation,
- bounded domains for prices, quantities, and order counts,
- why bounded exhaustive exploration is still informative,
- any modeling choices made for tractability,
- how order generation / actions are represented,
- which behaviors were modeled faithfully vs abstracted.

Important:
Be explicit that TLA+ was used to validate safety properties and semantic consistency, not to prove liveness or performance behavior.

### 4. Invariants and Properties Checked

Goal:
Show the paper is driven by concrete correctness properties.

Organize properties into categories:

- structural book invariants,
- fairness / ordering invariants,
- order-type invariants,
- STP safety invariants.

Examples:

- uncrossed book,
- no empty price levels,
- no ghost orders,
- only valid resting statuses,
- FIFO within a price level,
- no MARKET orders on book,
- no self-trades,
- no resting minQty constraints.

This section should include a compact table mapping each invariant to its meaning.

### 5. Main Finding: Triggered Stops Can Violate FIFO

This should be the centerpiece of the paper.

Required content:

- describe the intended FIFO invariant,
- explain the stop-triggering pipeline,
- show why keeping the original timestamp is semantically wrong once the stop becomes active,
- present the TLC counterexample as a short trace,
- explain the exact invalid end state,
- present the minimal repair: assign a fresh timestamp on trigger.

A figure or boxed trace is worth including here.

This section should be concrete and easy to follow even for readers who are not TLA+ experts.

### 6. Secondary Finding: STP DECREMENT and Iceberg Reload

This section should explain:

- how DECREMENT reduces both visible and remaining quantities,
- how the iceberg reload rule only fires after fills in the original spec,
- why DECREMENT can produce visibleQty = 0 with remainingQty > 0,
- why this strands quantity and breaks intended semantics.

Then show the repair:

- if visible quantity hits zero but remaining quantity remains positive and the order is an iceberg, reload the next visible slice and refresh its timestamp.

Again: keep the claim wording conservative unless an explicit failing TLC trace is available for the original model.

### 7. Additional Edge Cases and Design Lessons

Use this section to extract broader lessons.

Suggested framing:

- Most bugs emerged from interaction effects between independently reasonable features.
- Pre-check properties and execution-time effects can diverge.
- Fairness semantics often require explicit timestamp/priority rules at every conversion boundary.
- Feature composition deserves first-class treatment in exchange-style specs.

This is the right place to discuss:

- FOK plus STP DECREMENT,
- minQty plus STP DECREMENT,
- duplicated minQty clearing logic.

These should be presented as lessons or fragility points rather than oversold theorem-level results.

### 8. Spec Repairs

This section should summarize the minimal textual fixes.

It should not be long. A concise table is enough:

- issue,
- violated property,
- cause,
- repair.

The paper should emphasize that the fixes are small but semantically important.

### 9. Limitations and Threats to Validity

This section is mandatory.

Include:

- bounded state space only,
- abstraction from implementation details,
- no proof of implementation correctness,
- possible mismatch between generic spec and venue-specific exchange behavior,
- some findings may depend on modeling assumptions,
- large configurations were only partially explored.

This section increases credibility substantially.

### 10. Reproducibility

Describe:

- files in the artifact,
- TLC configurations,
- how to rerun the checks,
- what each configuration covers.

If the draft includes an artifact appendix, put exact commands there.

### 11. Conclusion

Keep it modest and direct:

Formalizing a realistic matcher specification in TLA+ was enough to uncover subtle but material semantic flaws before implementation. The main value came from making feature interactions explicit and checkable.

## Figures and tables to include

Claude should include these, even if only as simple text figures in the first draft:

1. A pipeline figure for order processing.
2. A short trace figure for the triggered-stop FIFO counterexample.
3. A table of invariants and their intent.
4. A table of TLC configurations and model-checking statistics.
5. A bug / consequence / fix summary table.

## Style guidance

The tone should be precise, modest, and technical.

Do:

- say "bounded exhaustive exploration" rather than "full proof",
- say "specification bug" rather than "implementation bug",
- say "within explored configurations",
- explain the counterexample in operational terms,
- make the lessons about feature composition explicit.

Do not:

- say the model proves the engine correct,
- claim unbounded verification,
- imply exchange-grade production validation,
- oversell observations as bugs if they are not demonstrated as such,
- bury the flagship FIFO result under too much background.

## Claims that are safe

These claims are supportable from the current materials:

- The specification is nontrivial and includes stops, STP, iceberg, MTL, post-only, minQty, and multiple time-in-force modes.
- TLC found a FIFO-related counterexample involving stop-trigger handling.
- The formalization process exposed another semantic issue involving STP DECREMENT and iceberg reload behavior.
- Several invariants passed within bounded configurations after fixes were applied.

## Claims to avoid or qualify heavily

- "The engine is verified."
- "The matcher is correct."
- "All bugs were found."
- "The approach scales to production-sized books" unless backed by data.
- "The second bug was found by TLC" unless the artifact clearly demonstrates that run on the unfixed model.

## Abstract blueprint

Claude should write an abstract with this shape:

1. One sentence on why advanced matching engines are hard to specify.
2. One sentence on formalizing the matcher in TLA+.
3. One sentence on the invariants checked and bounded exploration.
4. One sentence on the main counterexample: triggered stop orders violating FIFO.
5. One sentence on the secondary semantic issue and spec repairs.
6. One sentence on the broader lesson: formal methods are useful for feature-composition bugs in market mechanisms.

## Introduction blueprint

The introduction should do three things quickly:

1. Motivate the problem:
Matching engines look simple at the core, but realistic feature sets create subtle semantic interactions.

2. State the method:
The prose matcher specification was translated into TLA+ and checked with TLC under bounded configurations.

3. State the result:
Model checking exposed a FIFO violation caused by stop-trigger handling and uncovered another flaw around STP decrement and iceberg reloading.

End the introduction with a numbered list of contributions.

## Suggested contribution list wording

Claude can adapt this directly:

1. We present a TLA+ formalization of a feature-rich price-time-priority matching engine specification.
2. We define and check a suite of invariants covering book consistency, queue fairness, and order-type safety.
3. We report a concrete TLC counterexample showing that triggered stop orders can violate FIFO if activation does not refresh queue priority.
4. We identify an additional semantic flaw involving self-trade-prevention decrement and iceberg visibility management.
5. We derive minimal specification amendments and extract lessons about composing advanced order semantics.

## Suggested title options

Use titles that are accurate and not inflated.

Options:

- Formalizing a Price-Time Matching Engine in TLA+: A Case Study in Specification Bugs
- Model Checking a Feature-Rich Matching Engine Specification with TLA+
- Finding Semantic Bugs in a Matching Engine Specification Using TLA+
- A TLA+ Case Study of Price-Time Matching with Stops, STP, and Icebergs

## Prompt for Claude

Use this prompt as the drafting handoff:

```text
Write a short formal-methods case-study paper from this repo.

Goal:
Present this as a paper about using TLA+ to formalize and check a nontrivial price-time-priority matching-engine specification, leading to discovery of subtle semantic bugs and edge cases.

Primary sources:
- /home/aaslyan/matcher_tla/spec/REPORT.md
- /home/aaslyan/matcher_tla/spec/MatchingEngine.tla
- /home/aaslyan/matcher_tla/matching-engine-formal-spec.md

Requirements:
- Position it as a case study / experience report, not a grand theory paper.
- The flagship result is the TLC counterexample for FIFO violation caused by missing timestamp refresh on triggered stop orders.
- Treat the iceberg/STP issue carefully: call it a verified bug only if the artifacts support that claim directly; otherwise present it as a formalization-discovered spec hole.
- State bounded model checking limits explicitly.
- Distinguish specification verification from implementation verification.
- Use a modest, rigorous tone.

Structure:
1. Introduction
2. Matching-engine semantics under study
3. TLA+ model and bounded exploration
4. Invariants checked
5. Findings and counterexamples
6. Spec fixes
7. Lessons learned
8. Limitations and reproducibility
9. Conclusion

Include:
- a counterexample trace figure
- an invariants table
- a model-checking statistics table
- a bug/fix summary table

Optimize for clarity, technical credibility, and precise claims.
```

## Final instruction to Claude

Write for skeptical technical readers.

The paper should feel careful, concrete, and reproducible. The strongest version is not "formal methods are amazing." The strongest version is "here is a realistic specification, here is the exact counterexample, here is why normal prose review missed it, and here is the small fix."
