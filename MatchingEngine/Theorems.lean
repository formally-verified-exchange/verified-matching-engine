import MatchingEngine.Process
import MatchingEngine.Invariants

set_option maxHeartbeats 1000000

/-!
# Matching Engine — Invariant Preservation Theorems (Fresh Start)

This file is being rebuilt from scratch after we discovered that prior
versions were never being type-checked (the build target did not include
this file). Everything here must compile cleanly.

Key theorem: `process_preserves_uncrossed` — after processing an order,
the resulting book remains uncrossed.

**Note**: `BookUncrossed` checks only head prices. For the theorem to be
true, we also need the book's price levels to be sorted (otherwise
`doMatch` could consume a high head ask and advance to a lower one,
lowering `bestAsk` below `bestBid`). So the theorem takes sortedness
hypotheses.
-/

-- ============================================================================
-- Combined book invariant: uncrossed + sorted price levels
-- ============================================================================

/-- Combined book invariant: the book is uncrossed and its price levels
    are sorted on both sides. Both conditions are needed — `BookUncrossed`
    alone is not preserved by `doMatch` on unsorted books. -/
def AllInv (b : BookState) : Prop :=
  BookUncrossed b ∧
  bidsSortedDescB b.bids = true ∧
  asksSortedAscB b.asks = true

theorem AllInv.uncrossed {b : BookState} (h : AllInv b) : BookUncrossed b := h.1
theorem AllInv.bids_sorted {b : BookState} (h : AllInv b) :
    bidsSortedDescB b.bids = true := h.2.1
theorem AllInv.asks_sorted {b : BookState} (h : AllInv b) :
    asksSortedAscB b.asks = true := h.2.2

-- ============================================================================
-- BookUncrossed depends only on bids and asks
-- ============================================================================

/-- Two books with the same bids and asks have the same `BookUncrossed` value. -/
theorem BookUncrossed_of_bids_asks_eq {b1 b2 : BookState}
    (hb : b1.bids = b2.bids) (ha : b1.asks = b2.asks) :
    BookUncrossed b1 ↔ BookUncrossed b2 := by
  unfold BookUncrossed bestBidPrice bestAskPrice
  rw [hb, ha]

/-- Updating metadata fields preserves `BookUncrossed`. -/
theorem BookUncrossed_with_meta (b : BookState) (nid : OrderId) (clk : Timestamp) :
    BookUncrossed b ↔ BookUncrossed { b with nextId := nid, clock := clk } :=
  BookUncrossed_of_bids_asks_eq rfl rfl

-- ============================================================================
-- doMatch side isolation: buy preserves bids, sell preserves asks
-- ============================================================================

/-- For a buy order, `doMatch` never modifies the bids list. The contra side
    is asks, and doMatch only touches the contra side. -/
theorem doMatch_buy_preserves_bids (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hside : inc.side = .buy) :
    (doMatch fuel inc bids asks trades tm).bids = bids := by
  induction fuel generalizing inc asks trades tm with
  | zero => rfl
  | succ n ih =>
    unfold doMatch; simp only [hside]
    split
    · rfl
    · split
      · rfl
      · rename_i level restLevels
        split
        · rfl
        · split
          · exact ih _ _ _ _ (by first | rfl | exact hside)
          · rename_i _ resting restOrders _
            split
            · split <;> (first | exact ih _ _ _ _ (by first | rfl | exact hside) | rfl)
            · split
              · split
                · rfl
                · exact ih _ _ _ _ (by first | rfl | exact hside)
                · rfl
                · split
                  · exact ih _ _ _ _ (by first | rfl | exact hside)
                  · split
                    · exact ih _ _ _ _ (by first | rfl | exact hside)
                    · split
                      · exact ih _ _ _ _ (by first | rfl | exact hside)
                      · exact ih _ _ _ _ (by first | rfl | exact hside)
              · split
                · exact ih _ _ _ _ (by first | rfl | exact hside)
                · split
                  · exact ih _ _ _ _ (by first | rfl | exact hside)
                  · exact ih _ _ _ _ (by first | rfl | exact hside)

/-- Symmetric: for a sell order, `doMatch` never modifies the asks list. -/
theorem doMatch_sell_preserves_asks (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hside : inc.side = .sell) :
    (doMatch fuel inc bids asks trades tm).asks = asks := by
  induction fuel generalizing inc bids trades tm with
  | zero => rfl
  | succ n ih =>
    unfold doMatch; simp only [hside]
    split
    · rfl
    · split
      · rfl
      · rename_i level restLevels
        split
        · rfl
        · split
          · exact ih _ _ _ _ (by first | rfl | exact hside)
          · rename_i _ resting restOrders _
            split
            · split <;> (first | exact ih _ _ _ _ (by first | rfl | exact hside) | rfl)
            · split
              · split
                · rfl
                · exact ih _ _ _ _ (by first | rfl | exact hside)
                · rfl
                · split
                  · exact ih _ _ _ _ (by first | rfl | exact hside)
                  · split
                    · exact ih _ _ _ _ (by first | rfl | exact hside)
                    · split
                      · exact ih _ _ _ _ (by first | rfl | exact hside)
                      · exact ih _ _ _ _ (by first | rfl | exact hside)
              · split
                · exact ih _ _ _ _ (by first | rfl | exact hside)
                · split
                  · exact ih _ _ _ _ (by first | rfl | exact hside)
                  · exact ih _ _ _ _ (by first | rfl | exact hside)

-- ============================================================================
-- BookUncrossed metadata-irrelevance lemmas
-- ============================================================================

/-- Updating `stops` preserves `BookUncrossed`. -/
theorem BookUncrossed_with_stops (b : BookState) (s : List Order) :
    BookUncrossed b ↔ BookUncrossed { b with stops := s } :=
  BookUncrossed_of_bids_asks_eq rfl rfl

/-- Updating `lastTradePrice` preserves `BookUncrossed`. -/
theorem BookUncrossed_with_ltp (b : BookState) (p : Option Price) :
    BookUncrossed b ↔ BookUncrossed { b with lastTradePrice := p } :=
  BookUncrossed_of_bids_asks_eq rfl rfl

/-- Updating `clock` preserves `BookUncrossed`. -/
theorem BookUncrossed_with_clock (b : BookState) (c : Timestamp) :
    BookUncrossed b ↔ BookUncrossed { b with clock := c } :=
  BookUncrossed_of_bids_asks_eq rfl rfl

/-- If the asks side is empty, the book is uncrossed (no best ask to cross). -/
theorem BookUncrossed_no_asks (b : BookState) (h : b.asks = []) :
    BookUncrossed b := by
  unfold BookUncrossed bestAskPrice
  rw [h]; simp

/-- If the bids side is empty, the book is uncrossed (no best bid to cross). -/
theorem BookUncrossed_no_bids (b : BookState) (h : b.bids = []) :
    BookUncrossed b := by
  unfold BookUncrossed bestBidPrice
  rw [h]; simp

-- ============================================================================
-- AllInv lifted metadata helpers
-- ============================================================================

theorem AllInv.with_meta (b : BookState) (nid : OrderId) (clk : Timestamp)
    (h : AllInv b) : AllInv { b with nextId := nid, clock := clk } :=
  ⟨(BookUncrossed_with_meta b nid clk).mp h.1, h.2.1, h.2.2⟩

theorem AllInv.with_stops (b : BookState) (s : List Order)
    (h : AllInv b) : AllInv { b with stops := s } :=
  ⟨(BookUncrossed_with_stops b s).mp h.1, h.2.1, h.2.2⟩

theorem AllInv.with_ltp (b : BookState) (p : Option Price)
    (h : AllInv b) : AllInv { b with lastTradePrice := p } :=
  ⟨(BookUncrossed_with_ltp b p).mp h.1, h.2.1, h.2.2⟩

theorem AllInv.with_clock (b : BookState) (c : Timestamp)
    (h : AllInv b) : AllInv { b with clock := c } :=
  ⟨(BookUncrossed_with_clock b c).mp h.1, h.2.1, h.2.2⟩

-- ============================================================================
-- insertOrder side isolation
-- ============================================================================

/-- For a buy order, `insertOrder` only modifies bids. -/
theorem insertOrder_buy_preserves_asks (b : BookState) (o : Order) (hasTrades : Bool)
    (hside : o.side = .buy) :
    (insertOrder b o hasTrades).asks = b.asks := by
  unfold insertOrder
  match hsd : o.side with
  | .buy  => simp
  | .sell => exact absurd (hside.symm.trans hsd) (by decide)

/-- For a sell order, `insertOrder` only modifies asks. -/
theorem insertOrder_sell_preserves_bids (b : BookState) (o : Order) (hasTrades : Bool)
    (hside : o.side = .sell) :
    (insertOrder b o hasTrades).bids = b.bids := by
  unfold insertOrder
  match hsd : o.side with
  | .buy  => exact absurd (hside.symm.trans hsd) (by decide)
  | .sell => simp

/-- `insertOrder` never modifies stops. -/
theorem insertOrder_preserves_stops (b : BookState) (o : Order) (hasTrades : Bool) :
    (insertOrder b o hasTrades).stops = b.stops := by
  unfold insertOrder
  match o.side with
  | .buy  => rfl
  | .sell => rfl

/-- `dispose` never modifies stops. -/
theorem dispose_preserves_stops (inc : Order) (b : BookState) (trades : List Trade) :
    (dispose inc b trades).stops = b.stops := by
  unfold dispose
  split
  · rfl
  split
  · rfl
  split
  · rfl
  exact insertOrder_preserves_stops b inc _

-- ============================================================================
-- Level-modification helpers for asks/bids modification patterns in doMatch
-- ============================================================================

/-- Modified head-level + restLevels with the `if-isEmpty` pattern (as used
    by doMatch's skip/STP/decrement branches) preserves a per-level-price
    predicate `S`. -/
private theorem modLevelPrices {level : PriceLevel} {restLevels : List PriceLevel}
    {S : Price → Prop}
    (hlevel : S level.price)
    (hrest : ∀ l ∈ restLevels, S l.price)
    (ords : List Order) :
    ∀ l ∈ (if ords.isEmpty then restLevels
           else { level with orders := ords } :: restLevels), S l.price := by
  intro l hl
  split at hl
  · exact hrest l hl
  · cases hl with
    | head => exact hlevel
    | tail _ hmem => exact hrest l hmem

/-- Cons-only variant (used by normal fill's partial / iceberg cases). -/
private theorem consLevelPrices {level : PriceLevel} {restLevels : List PriceLevel}
    {S : Price → Prop}
    (hlevel : S level.price)
    (hrest : ∀ l ∈ restLevels, S l.price)
    (ords : List Order) :
    ∀ l ∈ ({ level with orders := ords } :: restLevels), S l.price := by
  intro l hl
  cases hl with
  | head => exact hlevel
  | tail _ hmem => exact hrest l hmem

-- ============================================================================
-- Minimal reproducer for the Lean 4.26 `simp only [hside]` issue
-- ============================================================================

/-- **REPRO**: This is the minimal shape that fails. It's identical to
    `doMatch_buy_preserves_bids` except the conclusion is a `∀ t ∈ ...`
    over trades with an abstract predicate `S`. The exact same
    `unfold doMatch; simp only [hside]` tactic works for the bids equality
    goal but fails here with `maximum number of steps exceeded`. -/
private theorem repro_simp_fails (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (S : Price → Prop) (hside : inc.side = .buy)
    (hacc : ∀ t ∈ trades, S t.price)
    (hasks : ∀ l ∈ asks, S l.price) :
    ∀ t ∈ (doMatch fuel inc bids asks trades tm).trades, S t.price := by
  induction fuel generalizing inc asks trades tm with
  | zero => unfold doMatch; exact hacc
  | succ n ih =>
    unfold doMatch
    split
    · exact hacc
    · split
      · -- inc.side = .buy branch
        cases hask : asks with
        | nil => exact hacc
        | cons level restLevels =>
          simp only
          -- level is the head of asks; level.price satisfies S
          rw [hask] at hasks
          have hlp : S level.price := hasks level (List.mem_cons_self)
          have hrp : ∀ l ∈ restLevels, S l.price := fun l hl =>
            hasks l (List.mem_cons_of_mem _ hl)
          split
          · exact hacc  -- !canMatchPrice: returns with trades unchanged
          · -- canMatchPrice: split on level.orders
            split
            · -- level.orders = []: skip to restLevels
              exact ih _ _ _ _ hside hacc hrp
            · -- level.orders = resting :: restOrders
              rename_i _ resting restOrders _
              split
              all_goals sorry
      · rename_i heq
        rw [hside] at heq
        exact absurd heq (by decide)

-- ============================================================================
-- Main theorem (STUB: reduces to processOrder_preserves_uncrossed)
-- ============================================================================

/-- SORRY: processOrder preserves `BookUncrossed`. This is the core obligation
    that will be proven via mutual induction over processOrder / processCascade
    / processTriggeredStops, with case analysis on the pipeline phases. -/
theorem processOrder_preserves_uncrossed (fuel : Nat) (o : Order) (b : BookState)
    (_h : AllInv b) :
    BookUncrossed (processOrder fuel o b).book := by
  sorry

/-- Main theorem: `process` preserves `BookUncrossed`. Reduces to
    `processOrder_preserves_uncrossed` since `process` only adds metadata
    updates (nextId, clock) on top of `processOrder`. -/
theorem process_preserves_uncrossed (b : BookState) (o : Order)
    (h : AllInv b) :
    BookUncrossed (process b o).book := by
  show BookUncrossed (process b o).book
  unfold process
  simp only
  exact (BookUncrossed_with_meta _ _ _).mp
    (processOrder_preserves_uncrossed defaultFuel _ b h)
