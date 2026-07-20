# Lean Proof Coverage of the §13 Invariant Suite

Status: **complete**. This file originally recorded the proof obligations
missing from `AllInv`; all of them are now proved in
`matcher_lean/MatchingEngine/TheoremsFull.lean`.

## Before

```lean
def AllInv (b : BookState) : Prop :=
  BookUncrossed b ∧
  bidsSortedDescB b.bids = true ∧
  asksSortedAscB b.asks = true
```

`Theorems.lean` (and independently `TheoremsElegant.lean`) proved that
`process` preserves `AllInv` — uncrossedness plus level sorting. The
remaining nine §13 invariants were defined but never proved preserved.

## Now

| ID | Invariant | Theorem |
| --- | --- | --- |
| INV-1 | No empty price levels | `process_preserves_FullBookInv` |
| INV-5 | No ghost resting orders | `process_preserves_FullBookInv` |
| INV-6 | Resting status consistency | `process_preserves_FullBookInv` |
| INV-7 | FIFO within each price level | `process_preserves_FullBookInv` |
| INV-8 | No resting market orders | `process_preserves_FullBookInv` |
| INV-11 | Post-only guarantee | `process_PostOnlyGuarantee` |
| INV-12 | STP guarantee | `process_STPGuarantee` |
| INV-13 | No resting MTL orders | `process_preserves_FullBookInv` |
| INV-14 | No resting minQty | `process_preserves_FullBookInv` |

`process_preserves_BookInvariant` is the capstone: it combines the `AllInv`
half from `Theorems.lean` with the seven book-state invariants above to give
the full `BookInvariant` of `Invariants.lean`. INV-11 and INV-12 stay
separate, as originally planned — the final book state does not retain the
emitted trades, so they are properties of `(process b o).trades`.

No `sorry` anywhere; the top-level results depend only on `propext`,
`Classical.choice` and `Quot.sound`.

## How the proof is structured (and why it differs from the original plan)

The plan proposed a flat `FullBookInv` conjunction threaded through the
induction. That does not work for INV-7. FIFO is **not preserved on its
own**: both queue-appending operations — iceberg reload in `doMatch` and
resting insertion in `insertOrder` — put an order at the back of a level, and
neither can be shown FIFO-safe without knowing the appended order is strictly
newer than everything already queued.

So the bundle is indexed by a timestamp bound instead:

```lean
def RestOk (n : Timestamp) (o : Order) : Prop :=
  0 < o.remainingQty ∧                                      -- INV-5
  (o.status = .new_ ∨ o.status = .partiallyFilled) ∧        -- INV-6
  o.orderType ≠ .market ∧                                   -- INV-8
  o.orderType ≠ .marketToLimit ∧                            -- INV-13
  o.minQty = none ∧                                         -- INV-14
  o.timestamp < n                                           -- supports INV-7

def LevelOk (n : Timestamp) (l : PriceLevel) : Prop :=
  l.orders ≠ [] ∧ FIFOLevel l.orders ∧ ∀ o ∈ l.orders, RestOk n o  -- INV-1, INV-7

def BookOk (b : BookState) : Prop := BookOkAt b.clock b
```

`BookOk` — every resting order is strictly older than the book clock — is
what actually carries through the induction. `FullBookInv` is then a
projection (`FullBookInv_of_BookOkAt`), not the induction invariant.

The clock arithmetic works out because `matchOrder` starts `doMatch` at
`b.clock + 1`, so a residual is always strictly older than the post-match
clock. The one exception is post-only insertion, which rests an order without
advancing the clock; that is the only reason `processOrder`'s postcondition
carries a `Nat.max`, and `process`'s closing `max (result.clock) (b.clock+1)`
bump is exactly what discharges it.

## Preconditions

```lean
def OrderRestOk (o : Order) : Prop :=
  0 < o.remainingQty ∧ (o.postOnly = true → o.orderType = OrderType.limit)

def StopsWF (b : BookState) : Prop :=
  ∀ s ∈ b.stops,
    (s.orderType = .stopLimit ∨ s.orderType = .stopMarket) ∧
    0 < s.remainingQty ∧ s.postOnly = false
```

`OrderRestOk` is implied by `Order.WellFormed`
(`OrderRestOk_of_WellFormed`): clause one is WF-1 with WF-11, clause two is
WF-13. `StopsWF` holds of the empty book and is preserved — `convertStop` is
the identity on non-stop order types, so without its first clause a
non-stop order parked in `.stops` would come back unchanged.

INV-11 and INV-12 need **no** preconditions: an order only reaches a matching
phase after failing the Phase 2 post-only test, so `aggPostOnly = false` holds
on every emitted trade by construction.

## Defect found while proving INV-13

Proving INV-13 required a third `OrderRestOk` clause, `MTL → minQty = none`,
which `Order.WellFormed` does **not** imply — i.e. the clause was hiding a
bug rather than recording a hypothesis.

`processOrder` evaluated the MinQty pre-check (Phase 3b) as an exclusive
`else if` that also performed match-and-dispose, so an MTL order carrying a
`minQty` never reached Phase 4 MTL routing and was disposed with its
`orderType` still `marketToLimit`. Since `dispose` refuses only MARKET
orders, it came to rest — violating INV-13 — and at price 0, because
`insertOrder` uses `o.price.getD 0` and WF-2b forces an MTL price to `none`.
Such an order is well formed: WF-8a permits MTL with GTC/DAY and WF-20
restricts `minQty` only on FOK.

Spec §12 Phase 3 is a **fall-through guard** — the quantity pre-checks run
"before any matching or routing" and only `RETURN` on failure. The C++ engine
implements it correctly (`engine.h:603`); Lean and TLA+ had both
mis-transcribed it. Fixed in `Process.lean` and `MatchingEngine.tla`;
regression test `test_bug3_mtlMinQty` in `Tests.lean`.

TLC could not have caught the TLA+ instance. `Dispose` binds `p == inc.price`,
which is `NULL` for an MTL order, and `[bQ EXCEPT ![NULL] = ...]` is a silent
no-op — the order vanishes instead of resting, and every invariant quantifies
over `p \in PRICES`, so nothing observes it. The warning is present in the
repo's own stored runs (`experiments/fast/raw/*__safety.txt`, "The EXCEPT was
applied to non-existing fields ... line 368"). Hardening `Dispose` against
this class of silent no-op is still open.

## Build closure

`lake build` did not check the proofs: `defaultTargets` named only the
`matchingengine` executable, rooted at `Main.lean`, so anything `Tests.lean`
did not transitively import was skipped. `lakefile.toml` now lists the
`MatchingEngine` library target as well. This also surfaced that
`TheoremsElegant.lean` had not compiled at HEAD (a malformed `Or.elim`
application at line 128), so the "two independent proofs of uncrossedness"
claim was not holding; both build now.
