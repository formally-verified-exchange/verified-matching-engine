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
-- doMatch passive price accumulator (buy side)
-- ============================================================================

/-- **The accumulator lemma for buy-side matching**.

    Given a predicate `S` on prices, if `S` holds on all existing trade
    prices and on all asks level prices, then after `doMatch` for a buy
    order, `S` holds on all trade prices in the result.

    **Implementation note**: avoids the Lean 4.26 `simp only [hside]; split`
    interaction that causes "maximum number of steps exceeded" errors. The
    workaround is to (1) skip `simp only [hside]` entirely, (2) use plain
    `split` to handle the inc-done check, (3) `split` again on the inc.side
    match (closing the sell branch by `rename_i heq; rw [hside] at heq;
    exact absurd heq (by decide)`), (4) `cases hask : asks with` for the
    contra match, (5) `rw [hask] at hasks` to align the hypothesis, (6)
    `simp only` (no args) for intermediate let/match reduction, then
    standard splits + IH applications use the helper lemmas
    `modLevelPrices` / `consLevelPrices`. -/
private theorem doMatch_passive_price_buy_acc (fuel : Nat) (inc : Order)
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
              -- resting.visibleQty == 0 && !selfTradeConflict (zero-visible skip)
              split
              · -- zero-visible true
                split  -- restOrders.isEmpty
                · -- true: asks' = restLevels
                  exact ih _ _ _ _ hside hacc hrp
                · -- false: asks' = {level with orders := restOrders} :: restLevels
                  exact ih _ _ _ _ hside hacc (consLevelPrices hlp hrp _)
              · -- zero-visible false: check STP conflict
                split
                · -- STP conflict: split on policy (4 branches)
                  split
                  · exact hacc  -- cancelNewest: returns unchanged
                  · -- cancelOldest: recurse with modified asks
                    split  -- restOrders.isEmpty
                    · exact ih _ _ _ _ hside hacc hrp
                    · exact ih _ _ _ _ hside hacc (consLevelPrices hlp hrp _)
                  · exact hacc  -- cancelBoth: returns unchanged
                  · -- decrement: 4 sub-cases
                    split  -- reduceQty == 0
                    · -- reduceQty = 0: stranded, remove
                      exact ih _ _ _ _ hside hacc (modLevelPrices hlp hrp _)
                    · -- reduceQty > 0
                      split  -- restRem == 0
                      · -- restRem = 0: fully decremented, remove
                        exact ih _ _ _ _ hside hacc (modLevelPrices hlp hrp _)
                      · -- restRem > 0
                        split  -- restVis == 0 && displayQty.isSome (iceberg reload)
                        · -- iceberg reload
                          exact ih _ _ _ _ hside hacc (modLevelPrices hlp hrp _)
                        · -- partial decrement
                          exact ih _ _ _ _ hside hacc (consLevelPrices hlp hrp _)
                · -- No STP: normal fill (3 sub-cases, each adds a new trade)
                  -- The new trade has price = level.price, so S level.price = hlp
                  -- gives us S on the new trade.
                  have hacc' : ∀ t ∈ trades ++ [{
                      price := level.price,
                      qty := min inc.remainingQty resting.visibleQty,
                      aggressorId := inc.id,
                      passiveId := resting.id,
                      aggressorSide := inc.side,
                      aggPostOnly := inc.postOnly,
                      aggStpGroup := inc.stpGroup,
                      pasStpGroup := resting.stpGroup }], S t.price := by
                    intro t ht
                    rw [List.mem_append] at ht
                    cases ht with
                    | inl h => exact hacc t h
                    | inr h =>
                      simp only [List.mem_singleton] at h
                      subst h
                      exact hlp
                  split  -- rest'.remainingQty == 0 (fully filled)
                  · -- fully filled: remove resting
                    exact ih _ _ _ _ hside hacc' (modLevelPrices hlp hrp _)
                  · split  -- rest'.visibleQty == 0 && displayQty.isSome (iceberg)
                    · -- iceberg reload
                      exact ih _ _ _ _ hside hacc' (consLevelPrices hlp hrp _)
                    · -- partial fill
                      exact ih _ _ _ _ hside hacc' (consLevelPrices hlp hrp _)
      · rename_i heq
        rw [hside] at heq
        exact absurd heq (by decide)

-- ============================================================================
-- doMatch result-asks accumulator (buy side)
-- ============================================================================

/-- For buy-side matching: any predicate `S` that holds on all input asks
    levels also holds on all output asks levels. Intuition: doMatch only
    modifies asks by removing/modifying levels (and adding reloaded
    icebergs at the same price), never by introducing a new price. -/
private theorem doMatch_buy_result_asks_acc (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (S : Price → Prop) (hside : inc.side = .buy)
    (hasks : ∀ l ∈ asks, S l.price) :
    ∀ l ∈ (doMatch fuel inc bids asks trades tm).asks, S l.price := by
  induction fuel generalizing inc asks trades tm with
  | zero => unfold doMatch; exact hasks
  | succ n ih =>
    unfold doMatch
    split
    · exact hasks
    · split
      · -- buy branch
        cases hask : asks with
        | nil =>
          -- asks = [] so result asks is also []; predicate is vacuous
          intro l hl
          exact absurd hl (by simp)
        | cons level restLevels =>
          simp only
          rw [hask] at hasks
          have hlp : S level.price := hasks level (List.mem_cons_self)
          have hrp : ∀ l ∈ restLevels, S l.price := fun l hl =>
            hasks l (List.mem_cons_of_mem _ hl)
          split
          · exact hasks  -- !canMatchPrice
          · split
            · -- level.orders = [] → recurse with restLevels
              exact ih _ _ _ _ hside hrp
            · -- level.orders = resting :: restOrders
              rename_i _ resting restOrders _
              split
              · -- zero-visible true
                split
                · exact ih _ _ _ _ hside hrp
                · exact ih _ _ _ _ hside (consLevelPrices hlp hrp _)
              · split
                · -- STP conflict
                  split
                  · exact hasks  -- cancelNewest: asks unchanged
                  · -- cancelOldest
                    split
                    · exact ih _ _ _ _ hside hrp
                    · exact ih _ _ _ _ hside (consLevelPrices hlp hrp _)
                  · -- cancelBoth: terminal but asks IS modified to level'
                    exact modLevelPrices hlp hrp _
                  · -- decrement
                    split
                    · exact ih _ _ _ _ hside (modLevelPrices hlp hrp _)
                    · split
                      · exact ih _ _ _ _ hside (modLevelPrices hlp hrp _)
                      · split
                        · exact ih _ _ _ _ hside (modLevelPrices hlp hrp _)
                        · exact ih _ _ _ _ hside (consLevelPrices hlp hrp _)
                · -- normal fill
                  split
                  · exact ih _ _ _ _ hside (modLevelPrices hlp hrp _)
                  · split
                    · exact ih _ _ _ _ hside (consLevelPrices hlp hrp _)
                    · exact ih _ _ _ _ hside (consLevelPrices hlp hrp _)
      · rename_i heq
        rw [hside] at heq; exact absurd heq (by decide)

-- ============================================================================
-- Sortedness helpers
-- ============================================================================

/-- For an asc-sorted price-level list, the head price is the minimum. -/
private theorem asksSortedAscB_head_min :
    ∀ (l : PriceLevel) (rest : List PriceLevel),
    asksSortedAscB (l :: rest) = true →
    ∀ l' ∈ (l :: rest), l.price ≤ l'.price := by
  intro l rest h
  induction rest generalizing l with
  | nil =>
    intro l' hl'
    cases hl' with
    | head => exact Nat.le_refl _
    | tail _ hh => cases hh
  | cons rh rt ih =>
    intro l' hl'
    cases hl' with
    | head => exact Nat.le_refl _
    | tail _ hmem =>
      -- From h: l.price < rh.price ∧ asksSortedAscB (rh :: rt)
      have hand : l.price < rh.price ∧ asksSortedAscB (rh :: rt) = true := by
        unfold asksSortedAscB at h
        rw [Bool.and_eq_true] at h
        exact ⟨of_decide_eq_true h.1, h.2⟩
      have := ih rh hand.2 l' hmem
      exact Nat.le_of_lt (Nat.lt_of_lt_of_le hand.1 this)

/-- For a desc-sorted price-level list, the head price is the maximum. -/
private theorem bidsSortedDescB_head_max :
    ∀ (l : PriceLevel) (rest : List PriceLevel),
    bidsSortedDescB (l :: rest) = true →
    ∀ l' ∈ (l :: rest), l'.price ≤ l.price := by
  intro l rest h
  induction rest generalizing l with
  | nil =>
    intro l' hl'
    cases hl' with
    | head => exact Nat.le_refl _
    | tail _ hh => cases hh
  | cons rh rt ih =>
    intro l' hl'
    cases hl' with
    | head => exact Nat.le_refl _
    | tail _ hmem =>
      have hand : l.price > rh.price ∧ bidsSortedDescB (rh :: rt) = true := by
        unfold bidsSortedDescB at h
        rw [Bool.and_eq_true] at h
        exact ⟨of_decide_eq_true h.1, h.2⟩
      have := ih rh hand.2 l' hmem
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt this hand.1)

-- ============================================================================
-- doMatch preserves uncrossed (buy side) — CRITICAL PATH lemma
-- ============================================================================

/-- For buy-side matching on a sorted+uncrossed book, the result book
    is still uncrossed. This is the central lemma needed by
    `processOrder_preserves_uncrossed`'s matching phases. -/
theorem doMatch_buy_preserves_uncrossed (fuel : Nat) (inc : Order) (b : BookState)
    (tm : Timestamp) (hside : inc.side = .buy) (h : AllInv b) :
    BookUncrossed { b with
      bids := (doMatch fuel inc b.bids b.asks [] tm).bids,
      asks := (doMatch fuel inc b.bids b.asks [] tm).asks } := by
  have hbids_eq : (doMatch fuel inc b.bids b.asks [] tm).bids = b.bids :=
    doMatch_buy_preserves_bids fuel inc b.bids b.asks [] tm hside
  unfold BookUncrossed bestBidPrice bestAskPrice
  simp only
  -- Case on the RESULT lists (not the input). This avoids the pain of
  -- input-list substitution not propagating into result-list expressions.
  cases h_resBids : (doMatch fuel inc b.bids b.asks [] tm).bids with
  | nil => simp
  | cons resBid resBidRest =>
    cases h_resAsks : (doMatch fuel inc b.bids b.asks [] tm).asks with
    | nil => simp
    | cons resAsk resAskRest =>
      simp only [List.head?_cons, Option.map_some]
      -- Goal: resBid.price < resAsk.price
      -- From hbids_eq + h_resBids: b.bids = resBid :: resBidRest
      have hb_bids : b.bids = resBid :: resBidRest := by
        rw [← hbids_eq]; exact h_resBids
      -- From original BookUncrossed: resBid.price < bestAsk(b)
      -- We need to know b.asks is non-empty (else uncrossed is vacuously true and
      -- we'd be in a contradiction since result asks is non-empty but doMatch
      -- can't add asks to empty input)
      cases hask : b.asks with
      | nil =>
        -- b.asks = []; doMatch with empty contra returns asks unchanged = []
        -- But we have h_resAsks : (doMatch ...).asks = resAsk :: resAskRest
        -- Need to derive a contradiction
        exfalso
        -- We need to show (doMatch fuel inc b.bids [] [] tm).asks = []
        -- This is the contra-empty case of doMatch.
        -- Easier: instantiate the asks accumulator with S := False
        -- Premise: ∀ l ∈ [], False — vacuous
        -- Conclusion: ∀ l ∈ result.asks, False
        -- Apply to resAsk to get False
        have hfalse := doMatch_buy_result_asks_acc fuel inc b.bids b.asks []
          tm (fun _ => False) hside (by intro l hl; rw [hask] at hl; cases hl)
        exact hfalse resAsk (by rw [h_resAsks]; exact List.mem_cons_self)
      | cons aHead aRest =>
        -- b.bids = resBid :: ..., b.asks = aHead :: ...
        -- From AllInv: resBid.price < aHead.price
        have huc : resBid.price < aHead.price := by
          have := h.1
          unfold BookUncrossed bestBidPrice bestAskPrice at this
          rw [hb_bids, hask] at this
          simp only [List.head?_cons, Option.map_some] at this
          exact this
        -- From sortedness: all of b.asks ≥ aHead.price
        have h_orig_asks : ∀ l ∈ b.asks, resBid.price < l.price := by
          intro l hl
          have hsorted := h.2.2
          rw [hask] at hsorted
          have hmin := asksSortedAscB_head_min aHead aRest hsorted l (by rw [hask] at hl; exact hl)
          exact Nat.lt_of_lt_of_le huc hmin
        -- Apply accumulator to get the predicate on result asks
        have h_res_asks := doMatch_buy_result_asks_acc fuel inc b.bids b.asks []
          tm (fun p => resBid.price < p) hside h_orig_asks
        -- resAsk is in the result asks
        exact h_res_asks resAsk (by rw [h_resAsks]; exact List.mem_cons_self)

-- ============================================================================
-- doMatch passive price rule (price-time priority)
-- ============================================================================

/-- Every trade produced by `doMatch` has price equal to the price of some
    resting level (either a bid or an ask). This is the price-time priority
    rule: aggressors trade at the resting (passive) order's price.

    **Note**: only the buy side is proven via the accumulator lemma.
    The sell side requires a symmetric `doMatch_passive_price_sell_acc`
    that mirrors the buy proof — deferred per the symmetry simplification. -/
theorem doMatch_passive_price (fuel : Nat) (inc : Order) (bids asks : List PriceLevel)
    (tm : Timestamp) :
    ∀ t ∈ (doMatch fuel inc bids asks [] tm).trades,
      ∃ l, (l ∈ bids ∨ l ∈ asks) ∧ t.price = l.price := by
  cases hs : inc.side with
  | buy =>
    exact doMatch_passive_price_buy_acc fuel inc bids asks [] tm
      (fun p => ∃ l, (l ∈ bids ∨ l ∈ asks) ∧ p = l.price) hs
      (fun _ h => absurd h List.not_mem_nil)
      (fun l hl => ⟨l, Or.inr hl, rfl⟩)
  | sell =>
    -- Symmetric to buy via doMatch_passive_price_sell_acc; deferred.
    sorry

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
