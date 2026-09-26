import MatchingEngine.Process
import MatchingEngine.Invariants
import MatchingEngine.Theorems
import MatchingEngine.TheoremsFull

/-!
# Reachable-State Corollary

`process_preserves_BookInvariant` (`TheoremsFull.lean`) is a **single-step**
theorem: if a book already satisfies a precondition bundle, then after
processing one order, `BookInvariant` holds for the result. The paper's
headline claim is stronger — that `BookInvariant` holds for *every* book
reachable from the empty book via an arbitrary sequence of well-formed
orders.

The composition needs a *loop invariant*: a predicate bundle strong enough
that (a) the empty book satisfies it, and (b) if it holds before processing
one more order, it still holds after. `process_preserves_BookInvariant`'s own
hypotheses (`AllInv`, `BookOk`, `StopsWF`) are exactly that bundle, plus
`StopsNoPostOnly` (needed to re-invoke `AllInv` preservation on the next
step). Call it `ProcessInv`.

## Status

- `AllInv_empty`, `StopsNoPostOnly_empty`, `ProcessInv_empty` — PROVED (the
  empty book trivially satisfies the bundle).
- `process_preserves_AllInv`, `process_preserves_StopsNoPostOnly` — PROVED in `Theorems.lean`.
- `ProcessInv_step`, `ProcessInv_foldl` — PROVED by list induction.
- `BookInvariant_of_ProcessInv` — PROVED: `ProcessInv` implies `BookInvariant`.
- `process_all_preserves_BookInvariant` — PROVED: for any sequence of well-formed orders,
  the resulting reachable book satisfies `BookInvariant`.
-/

/-- Fold-friendly form of `process`: just the resulting book, discarding the
    emitted trades. -/
def processBook (b : BookState) (o : Order) : BookState := (process b o).book

/-- The loop invariant: the precondition bundle needed to invoke
    `process_preserves_BookInvariant` again on the *next* order. -/
def ProcessInv (b : BookState) : Prop :=
  AllInv b ∧ BookOk b ∧ StopsWF b ∧ StopsNoPostOnly b

theorem AllInv_empty : AllInv BookState.empty :=
  ⟨BookUncrossed_no_asks BookState.empty rfl, rfl, rfl⟩

theorem StopsNoPostOnly_empty : StopsNoPostOnly BookState.empty := by
  intro s hs
  cases hs

/-- The empty book satisfies the loop invariant (base case). -/
theorem ProcessInv_empty : ProcessInv BookState.empty :=
  ⟨AllInv_empty, BookOk_empty, StopsWF_empty, StopsNoPostOnly_empty⟩

/-- The loop invariant is preserved by one call to `process` (inductive
    step). -/
theorem ProcessInv_step (b : BookState) (o : Order)
    (hinv : ProcessInv b) (hpok : OrderProcOk o) (hok : OrderRestOk o) :
    ProcessInv (process b o).book := by
  obtain ⟨hall, hb, hstopsWF, hsnp⟩ := hinv
  exact ⟨process_preserves_AllInv b o hpok hsnp hall,
    (process_preserves_BookOk b o hb hstopsWF hok).1,
    (process_preserves_BookOk b o hb hstopsWF hok).2,
    process_preserves_StopsNoPostOnly b o hpok hsnp hall⟩

/-- The loop invariant survives folding `process` over any list of orders
    that are individually well-formed enough to invoke `process`. Proved
    by list induction. -/
theorem ProcessInv_foldl (orders : List Order) (b : BookState)
    (hinv : ProcessInv b)
    (hwf : ∀ o ∈ orders, OrderProcOk o ∧ OrderRestOk o) :
    ProcessInv (orders.foldl processBook b) := by
  induction orders generalizing b with
  | nil => exact hinv
  | cons o rest ih =>
    have ho := hwf o List.mem_cons_self
    have hstep : ProcessInv (processBook b o) :=
      ProcessInv_step b o hinv ho.1 ho.2
    have hrest : ∀ o' ∈ rest, OrderProcOk o' ∧ OrderRestOk o' :=
      fun o' hmem => hwf o' (List.mem_cons_of_mem o hmem)
    exact ih (processBook b o) hstep hrest

/-- Every state satisfying the loop invariant `ProcessInv` also satisfies the
    full §13 `BookInvariant`. -/
theorem BookInvariant_of_ProcessInv {b : BookState} (hinv : ProcessInv b) :
    BookInvariant b := by
  obtain ⟨hall, hb, -, -⟩ := hinv
  obtain ⟨hne, hng, hsc, hfifo, hnm, hnmtl, hnmq⟩ := FullBookInv_of_BookOkAt hb
  exact ⟨hall.1, hng, hsc, hnm, hnmtl, hnmq, hne, hfifo⟩

/-- **The reachable-state corollary.** For any finite sequence of orders that
    are each well-formed enough to invoke `process` (`OrderProcOk`,
    `OrderRestOk` — both implied by `Order.WellFormed` via
    `OrderRestOk_of_WellFormed` and the `OrderProcOk` projection), the book
    reached by processing them one at a time from the empty book satisfies
    the full §13 `BookInvariant`. This is the theorem the paper's summary
    cites for the multi-step / reachable-state reading of the result. -/
theorem process_all_preserves_BookInvariant (orders : List Order)
    (hwf : ∀ o ∈ orders, OrderProcOk o ∧ OrderRestOk o) :
    BookInvariant (orders.foldl processBook BookState.empty) :=
  BookInvariant_of_ProcessInv (ProcessInv_foldl orders BookState.empty ProcessInv_empty hwf)
