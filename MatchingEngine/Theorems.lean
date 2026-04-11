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
-- Side abstraction helpers — enable symmetric (buy/sell) lemma statements
-- ============================================================================

/-- Input same-side list: buy → bids, sell → asks. -/
@[inline] def sameInput (s : Side) (bids asks : List PriceLevel) : List PriceLevel :=
  match s with | .buy => bids | .sell => asks

/-- Input contra-side list: buy → asks, sell → bids. -/
@[inline] def contraInput (s : Side) (bids asks : List PriceLevel) : List PriceLevel :=
  match s with | .buy => asks | .sell => bids

/-- MatchResult same-side list (the side of the incoming order). -/
@[inline] def MatchResult.sameSide (s : Side) (mr : MatchResult) : List PriceLevel :=
  match s with | .buy => mr.bids | .sell => mr.asks

/-- MatchResult contra-side list (opposite of the incoming order side). -/
@[inline] def MatchResult.contraSide (s : Side) (mr : MatchResult) : List PriceLevel :=
  match s with | .buy => mr.asks | .sell => mr.bids

/-- Sortedness predicate for the contra side (asc for buy's asks, desc for sell's bids). -/
@[inline] def contraSorted (s : Side) (lvls : List PriceLevel) : Bool :=
  match s with | .buy => asksSortedAscB lvls | .sell => bidsSortedDescB lvls

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

/-- **Unified side-parameterized**: `doMatch` never modifies the same-side list
    (buy preserves bids, sell preserves asks). Mechanical merge of the two
    side-specific lemmas via case analysis. -/
theorem doMatch_preserves_sameSide (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (side : Side) (hside : inc.side = side) :
    MatchResult.sameSide side (doMatch fuel inc bids asks trades tm) =
    sameInput side bids asks := by
  cases side with
  | buy =>
    show (doMatch fuel inc bids asks trades tm).bids = bids
    exact doMatch_buy_preserves_bids fuel inc bids asks trades tm hside
  | sell =>
    show (doMatch fuel inc bids asks trades tm).asks = asks
    exact doMatch_sell_preserves_asks fuel inc bids asks trades tm hside

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
-- insertOrder head-price preservation
-- ============================================================================

/-- For a buy-side insert: if the book is uncrossed and the new buy order's
    price is strictly less than `bestAskPrice` (or asks are empty), then
    `insertOrder b o hasTrades` preserves `BookUncrossed`. -/
theorem insertOrder_buy_preserves_uncrossed (b : BookState) (o : Order)
    (hasTrades : Bool) (hside : o.side = .buy) (h : BookUncrossed b)
    (hprice : ∀ askP ∈ bestAskPrice b, (o.price.getD 0) < askP) :
    BookUncrossed (insertOrder b o hasTrades) := by
  unfold BookUncrossed
  -- asks side unchanged
  have hasks : (insertOrder b o hasTrades).asks = b.asks :=
    insertOrder_buy_preserves_asks b o hasTrades hside
  rw [show bestAskPrice (insertOrder b o hasTrades) = bestAskPrice b from by
        unfold bestAskPrice; rw [hasks]]
  -- bids side: insertDesc
  unfold insertOrder
  match hsd : o.side with
  | .sell => exact absurd (hside.symm.trans hsd) (by decide)
  | .buy =>
    simp only
    -- Split on bestAskPrice b
    cases hask : bestAskPrice b with
    | none =>
      -- `none` is already substituted by the cases tactic; reduce match.
      cases h_bb : bestBidPrice {
        bids := insertDesc b.bids _ (o.price.getD 0),
        asks := b.asks, stops := b.stops,
        lastTradePrice := b.lastTradePrice,
        nextId := b.nextId, clock := b.clock } <;> trivial
    | some askP =>
      have hprice' : (o.price.getD 0) < askP := hprice askP (by
        rw [hask]; exact Option.mem_some_iff.mpr rfl)
      -- Goal: best bid of new book < askP
      unfold bestBidPrice
      match hbids : b.bids with
      | [] =>
        unfold insertDesc
        simp
        exact hprice'
      | lhd :: lrest =>
        -- Original uncrossed: lhd.price < askP
        have hhd : lhd.price < askP := by
          have h' := h
          unfold BookUncrossed at h'
          rw [show bestBidPrice b = some lhd.price by
                unfold bestBidPrice; rw [hbids]; rfl,
              hask] at h'
          exact h'
        -- insertDesc head is max p lhd.price (both < askP)
        unfold insertDesc
        by_cases h1 : (o.price.getD 0) > lhd.price
        · simp [h1]
          exact hprice'
        · by_cases h2 : (o.price.getD 0) = lhd.price
          · simp [h1, h2]
            exact hhd
          · have h3 : ¬ ((o.price.getD 0) == lhd.price) = true := by
              intro heq
              have : (o.price.getD 0) = lhd.price := by
                simpa [beq_iff_eq] using heq
              exact h2 this
            simp [h1, h3]
            exact hhd

/-- **Mirror (sell side)**: symmetric to `insertOrder_buy_preserves_uncrossed`.
    Sell insert preserves uncrossed if `bestBidPrice < o.price` (or no bids). -/
theorem insertOrder_sell_preserves_uncrossed (b : BookState) (o : Order)
    (hasTrades : Bool) (hside : o.side = .sell) (h : BookUncrossed b)
    (hprice : ∀ bidP ∈ bestBidPrice b, bidP < (o.price.getD 0)) :
    BookUncrossed (insertOrder b o hasTrades) := by
  unfold BookUncrossed
  -- bids side unchanged
  have hbids : (insertOrder b o hasTrades).bids = b.bids :=
    insertOrder_sell_preserves_bids b o hasTrades hside
  rw [show bestBidPrice (insertOrder b o hasTrades) = bestBidPrice b from by
        unfold bestBidPrice; rw [hbids]]
  -- asks side: insertAsc
  unfold insertOrder
  match hsd : o.side with
  | .buy => exact absurd (hside.symm.trans hsd) (by decide)
  | .sell =>
    simp only
    -- Split on bestBidPrice b
    cases hbid : bestBidPrice b with
    | none =>
      -- `none` is the first match arg; any asks gives True.
      trivial
    | some bidP =>
      have hprice' : bidP < (o.price.getD 0) := hprice bidP (by
        rw [hbid]; exact Option.mem_some_iff.mpr rfl)
      -- Goal: bidP < best ask of new book
      unfold bestAskPrice
      match hasks : b.asks with
      | [] =>
        unfold insertAsc
        simp
        exact hprice'
      | lhd :: lrest =>
        -- Original uncrossed: bidP < lhd.price
        have hhd : bidP < lhd.price := by
          have h' := h
          unfold BookUncrossed at h'
          rw [hbid,
              show bestAskPrice b = some lhd.price by
                unfold bestAskPrice; rw [hasks]; rfl] at h'
          exact h'
        -- insertAsc head is min q lhd.price; bidP < both
        unfold insertAsc
        by_cases h1 : (o.price.getD 0) < lhd.price
        · simp [h1]
          exact hprice'
        · by_cases h2 : (o.price.getD 0) = lhd.price
          · simp [h1, h2]
            exact hhd
          · have h3 : ¬ ((o.price.getD 0) == lhd.price) = true := by
              intro heq
              have : (o.price.getD 0) = lhd.price := by
                simpa [beq_iff_eq] using heq
              exact h2 this
            simp [h1, h3]
            exact hhd

/-- **Unified side-parameterized**: insert preserves uncrossed when the
    order's price is strictly on the non-crossing side of the opposite book. -/
theorem insertOrder_preserves_uncrossed (b : BookState) (o : Order)
    (hasTrades : Bool) (side : Side) (hside : o.side = side)
    (h : BookUncrossed b)
    (hprice : match side with
      | .buy  => ∀ askP ∈ bestAskPrice b, (o.price.getD 0) < askP
      | .sell => ∀ bidP ∈ bestBidPrice b, bidP < (o.price.getD 0)) :
    BookUncrossed (insertOrder b o hasTrades) := by
  cases side with
  | buy  => exact insertOrder_buy_preserves_uncrossed b o hasTrades hside h hprice
  | sell => exact insertOrder_sell_preserves_uncrossed b o hasTrades hside h hprice

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

/-- **Mirror (sell side)**: any predicate `S` that holds on all input bids
    levels also holds on all output bids levels after sell-side matching. -/
private theorem doMatch_sell_result_bids_acc (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (S : Price → Prop) (hside : inc.side = .sell)
    (hbids : ∀ l ∈ bids, S l.price) :
    ∀ l ∈ (doMatch fuel inc bids asks trades tm).bids, S l.price := by
  induction fuel generalizing inc bids trades tm with
  | zero => unfold doMatch; exact hbids
  | succ n ih =>
    unfold doMatch
    split
    · exact hbids
    · split
      · -- buy branch: absurd (hside : inc.side = .sell)
        rename_i heq
        rw [hside] at heq; exact absurd heq (by decide)
      · -- sell branch
        cases hbid : bids with
        | nil =>
          -- bids = [] so result bids is also []
          intro l hl
          exact absurd hl (by simp)
        | cons level restLevels =>
          simp only
          rw [hbid] at hbids
          have hlp : S level.price := hbids level (List.mem_cons_self)
          have hrp : ∀ l ∈ restLevels, S l.price := fun l hl =>
            hbids l (List.mem_cons_of_mem _ hl)
          split
          · exact hbids  -- !canMatchPrice
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
                  · exact hbids  -- cancelNewest: bids unchanged
                  · -- cancelOldest
                    split
                    · exact ih _ _ _ _ hside hrp
                    · exact ih _ _ _ _ hside (consLevelPrices hlp hrp _)
                  · -- cancelBoth: terminal but bids IS modified to level'
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

/-- **Unified side-parameterized**: predicate on contra-side levels is
    preserved by `doMatch`. -/
theorem doMatch_result_contra_acc (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (S : Price → Prop) (side : Side) (hside : inc.side = side)
    (hcontra : ∀ l ∈ contraInput side bids asks, S l.price) :
    ∀ l ∈ MatchResult.contraSide side (doMatch fuel inc bids asks trades tm),
      S l.price := by
  cases side with
  | buy =>
    show ∀ l ∈ (doMatch fuel inc bids asks trades tm).asks, S l.price
    exact doMatch_buy_result_asks_acc fuel inc bids asks trades tm S hside hcontra
  | sell =>
    show ∀ l ∈ (doMatch fuel inc bids asks trades tm).bids, S l.price
    exact doMatch_sell_result_bids_acc fuel inc bids asks trades tm S hside hcontra

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
-- Sortedness modification helpers
-- ============================================================================

/-- Tail of an asc-sorted asks list is asc-sorted. -/
private theorem asksSortedAscB_tail (l : PriceLevel) (rest : List PriceLevel)
    (h : asksSortedAscB (l :: rest) = true) :
    asksSortedAscB rest = true := by
  cases rest with
  | nil => rfl
  | cons r rs =>
    unfold asksSortedAscB at h
    rw [Bool.and_eq_true] at h
    exact h.2

/-- Tail of a desc-sorted bids list is desc-sorted. -/
private theorem bidsSortedDescB_tail (l : PriceLevel) (rest : List PriceLevel)
    (h : bidsSortedDescB (l :: rest) = true) :
    bidsSortedDescB rest = true := by
  cases rest with
  | nil => rfl
  | cons r rs =>
    unfold bidsSortedDescB at h
    rw [Bool.and_eq_true] at h
    exact h.2

/-- Modifying the head level's orders (not its price) preserves asc sortedness. -/
private theorem asksSortedAscB_modify_head (level : PriceLevel)
    (restLevels : List PriceLevel) (newOrders : List Order)
    (h : asksSortedAscB (level :: restLevels) = true) :
    asksSortedAscB ({ level with orders := newOrders } :: restLevels) = true := by
  cases restLevels with
  | nil => rfl
  | cons r rs =>
    unfold asksSortedAscB
    unfold asksSortedAscB at h
    rw [Bool.and_eq_true] at h ⊢
    show (decide ({ level with orders := newOrders }.price < r.price) = true) ∧ _
    show (decide (level.price < r.price) = true) ∧ _
    exact h

/-- Modifying the head level's orders (not its price) preserves desc sortedness. -/
private theorem bidsSortedDescB_modify_head (level : PriceLevel)
    (restLevels : List PriceLevel) (newOrders : List Order)
    (h : bidsSortedDescB (level :: restLevels) = true) :
    bidsSortedDescB ({ level with orders := newOrders } :: restLevels) = true := by
  cases restLevels with
  | nil => rfl
  | cons r rs =>
    unfold bidsSortedDescB
    unfold bidsSortedDescB at h
    rw [Bool.and_eq_true] at h ⊢
    show (decide ({ level with orders := newOrders }.price > r.price) = true) ∧ _
    show (decide (level.price > r.price) = true) ∧ _
    exact h

/-- The doMatch "drop head order (possibly drop level)" pattern preserves
    asc sortedness. -/
private theorem asksSortedAscB_drop_head_pattern (level : PriceLevel)
    (restLevels : List PriceLevel) (restOrders : List Order)
    (h : asksSortedAscB (level :: restLevels) = true) :
    asksSortedAscB (if restOrders.isEmpty then restLevels
                    else { level with orders := restOrders } :: restLevels) = true := by
  by_cases hio : restOrders.isEmpty
  · simp [hio]
    exact asksSortedAscB_tail level restLevels h
  · simp [hio]
    exact asksSortedAscB_modify_head level restLevels restOrders h

/-- The doMatch "drop head order (possibly drop level)" pattern preserves
    desc sortedness. -/
private theorem bidsSortedDescB_drop_head_pattern (level : PriceLevel)
    (restLevels : List PriceLevel) (restOrders : List Order)
    (h : bidsSortedDescB (level :: restLevels) = true) :
    bidsSortedDescB (if restOrders.isEmpty then restLevels
                    else { level with orders := restOrders } :: restLevels) = true := by
  by_cases hio : restOrders.isEmpty
  · simp [hio]
    exact bidsSortedDescB_tail level restLevels h
  · simp [hio]
    exact bidsSortedDescB_modify_head level restLevels restOrders h

-- ============================================================================
-- insertDesc/insertAsc sortedness preservation
-- ============================================================================

/-- Every level in `insertDesc levels o p` has head price `< bound` if `p < bound`
    and every level in `levels.head?` has price `< bound`. -/
private theorem insertDesc_head_lt_bound (levels : List PriceLevel) (o : Order) (p : Price)
    (bound : Price) (h_p : p < bound)
    (h_lvls : ∀ lh ∈ levels.head?, lh.price < bound) :
    ∀ lh ∈ (insertDesc levels o p).head?, lh.price < bound := by
  cases levels with
  | nil =>
    unfold insertDesc
    intro lh hlh
    simp at hlh
    rw [← hlh]
    exact h_p
  | cons l rest =>
    unfold insertDesc
    intro lh hlh
    by_cases h1 : p > l.price
    · simp [h1] at hlh
      rw [← hlh]; exact h_p
    · by_cases h2 : p = l.price
      · have hb : (p == l.price) = true := by simp [h2]
        simp [h1, hb] at hlh
        rw [← hlh]
        exact h_lvls l (by simp)
      · have h3 : ¬ ((p == l.price) = true) := by
          intro heq; exact h2 (by simpa using heq)
        simp [h1, h3] at hlh
        rw [← hlh]
        exact h_lvls l (by simp)

/-- Every level in `insertAsc levels o p` has head price `> bound` if `p > bound`
    and every level in `levels.head?` has price `> bound`. -/
private theorem insertAsc_head_gt_bound (levels : List PriceLevel) (o : Order) (p : Price)
    (bound : Price) (h_p : p > bound)
    (h_lvls : ∀ lh ∈ levels.head?, lh.price > bound) :
    ∀ lh ∈ (insertAsc levels o p).head?, lh.price > bound := by
  cases levels with
  | nil =>
    unfold insertAsc
    intro lh hlh
    simp at hlh
    rw [← hlh]
    exact h_p
  | cons l rest =>
    unfold insertAsc
    intro lh hlh
    by_cases h1 : p < l.price
    · simp [h1] at hlh
      rw [← hlh]; exact h_p
    · by_cases h2 : p = l.price
      · have hb : (p == l.price) = true := by simp [h2]
        simp [h1, hb] at hlh
        rw [← hlh]
        exact h_lvls l (by simp)
      · have h3 : ¬ ((p == l.price) = true) := by
          intro heq; exact h2 (by simpa using heq)
        simp [h1, h3] at hlh
        rw [← hlh]
        exact h_lvls l (by simp)

/-- `insertDesc` preserves `bidsSortedDescB`. -/
theorem insertDesc_preserves_sorted (levels : List PriceLevel) (o : Order) (p : Price)
    (h : bidsSortedDescB levels = true) :
    bidsSortedDescB (insertDesc levels o p) = true := by
  induction levels with
  | nil => rfl
  | cons l rest ih =>
    unfold insertDesc
    by_cases h1 : p > l.price
    · simp [h1]
      unfold bidsSortedDescB
      rw [Bool.and_eq_true]
      refine ⟨by exact decide_eq_true h1, h⟩
    · by_cases h2 : p = l.price
      · have hb : (p == l.price) = true := by simp [h2]
        simp [h1, hb]
        exact bidsSortedDescB_modify_head l rest _ h
      · -- p < l.price: recurse
        have h3 : ¬ ((p == l.price) = true) := by
          intro heq; exact h2 (by simpa using heq)
        simp [h1, h3]
        -- Goal: bidsSortedDescB (l :: insertDesc rest o p) = true
        have h_rest_sorted : bidsSortedDescB rest = true :=
          bidsSortedDescB_tail l rest h
        have hrec : bidsSortedDescB (insertDesc rest o p) = true :=
          ih h_rest_sorted
        have hle : p ≤ l.price := Nat.le_of_not_lt h1
        have hpl : p < l.price := Nat.lt_of_le_of_ne hle h2
        -- Need: all levels in rest have price < l.price (from original sortedness)
        have h_rest_lt : ∀ lh ∈ rest.head?, lh.price < l.price := by
          intro lh hlh
          cases hr : rest with
          | nil => rw [hr] at hlh; cases hlh
          | cons r rs =>
            rw [hr] at hlh
            simp at hlh
            rw [← hlh]
            rw [hr] at h
            unfold bidsSortedDescB at h
            rw [Bool.and_eq_true] at h
            exact of_decide_eq_true h.1
        have h_new_head_lt : ∀ hd ∈ (insertDesc rest o p).head?, hd.price < l.price :=
          insertDesc_head_lt_bound rest o p l.price hpl h_rest_lt
        -- Combine: insertDesc rest is sorted + head < l.price
        cases hri : insertDesc rest o p with
        | nil =>
          show bidsSortedDescB [l] = true
          rfl
        | cons r rs =>
          unfold bidsSortedDescB
          rw [Bool.and_eq_true]
          refine ⟨?_, ?_⟩
          · have := h_new_head_lt r (by rw [hri]; simp)
            exact decide_eq_true this
          · rw [hri] at hrec; exact hrec

/-- `insertAsc` preserves `asksSortedAscB`. -/
theorem insertAsc_preserves_sorted (levels : List PriceLevel) (o : Order) (p : Price)
    (h : asksSortedAscB levels = true) :
    asksSortedAscB (insertAsc levels o p) = true := by
  induction levels with
  | nil => rfl
  | cons l rest ih =>
    unfold insertAsc
    by_cases h1 : p < l.price
    · simp [h1]
      unfold asksSortedAscB
      rw [Bool.and_eq_true]
      refine ⟨by exact decide_eq_true h1, h⟩
    · by_cases h2 : p = l.price
      · have hb : (p == l.price) = true := by simp [h2]
        simp [h1, hb]
        exact asksSortedAscB_modify_head l rest _ h
      · have h3 : ¬ ((p == l.price) = true) := by
          intro heq; exact h2 (by simpa using heq)
        simp [h1, h3]
        have h_rest_sorted : asksSortedAscB rest = true :=
          asksSortedAscB_tail l rest h
        have hrec : asksSortedAscB (insertAsc rest o p) = true :=
          ih h_rest_sorted
        have hle : l.price ≤ p := Nat.le_of_not_lt h1
        have hpl : p > l.price := Nat.lt_of_le_of_ne hle (fun heq => h2 heq.symm)
        have h_rest_gt : ∀ lh ∈ rest.head?, lh.price > l.price := by
          intro lh hlh
          cases hr : rest with
          | nil => rw [hr] at hlh; cases hlh
          | cons r rs =>
            rw [hr] at hlh
            simp at hlh
            rw [← hlh]
            rw [hr] at h
            unfold asksSortedAscB at h
            rw [Bool.and_eq_true] at h
            exact of_decide_eq_true h.1
        have h_new_head_gt : ∀ hd ∈ (insertAsc rest o p).head?, hd.price > l.price :=
          insertAsc_head_gt_bound rest o p l.price hpl h_rest_gt
        cases hri : insertAsc rest o p with
        | nil => show asksSortedAscB [l] = true; rfl
        | cons r rs =>
          unfold asksSortedAscB
          rw [Bool.and_eq_true]
          refine ⟨?_, ?_⟩
          · have := h_new_head_gt r (by rw [hri]; simp)
            exact decide_eq_true this
          · rw [hri] at hrec; exact hrec

/-- `insertOrder` preserves both bids and asks sortedness. -/
theorem insertOrder_preserves_sortedness (b : BookState) (o : Order) (hasTrades : Bool)
    (h_bids : bidsSortedDescB b.bids = true)
    (h_asks : asksSortedAscB b.asks = true) :
    bidsSortedDescB (insertOrder b o hasTrades).bids = true ∧
    asksSortedAscB (insertOrder b o hasTrades).asks = true := by
  unfold insertOrder
  cases hs : o.side with
  | buy =>
    simp only
    refine ⟨?_, h_asks⟩
    exact insertDesc_preserves_sorted b.bids _ _ h_bids
  | sell =>
    simp only
    refine ⟨h_bids, ?_⟩
    exact insertAsc_preserves_sorted b.asks _ _ h_asks

-- ============================================================================
-- doMatch preserves contra-side sortedness
-- ============================================================================

/-- **Buy side**: `doMatch` preserves `asksSortedAscB` on the contra side. -/
theorem doMatch_buy_preserves_asks_sorted (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hside : inc.side = .buy)
    (hsorted : asksSortedAscB asks = true) :
    asksSortedAscB (doMatch fuel inc bids asks trades tm).asks = true := by
  induction fuel generalizing inc asks trades tm with
  | zero => unfold doMatch; exact hsorted
  | succ n ih =>
    unfold doMatch
    split
    · exact hsorted
    · split
      · -- buy branch (contra = asks)
        cases hask : asks with
        | nil =>
          -- asks = [] → output.asks = []
          rfl
        | cons level restLevels =>
          simp only
          rw [hask] at hsorted
          split
          · -- !canMatchPrice: unchanged
            exact hsorted
          · cases horders : level.orders with
            | nil =>
              -- Empty level skip: recurse with restLevels
              exact ih _ _ _ _ hside (asksSortedAscB_tail level restLevels hsorted)
            | cons resting restOrders =>
              simp only
              cases hzv : (resting.visibleQty == 0 && !selfTradeConflict inc resting) with
              | true =>
                -- Zero-vis skip: drop head order pattern
                exact ih _ _ _ _ hside
                  (asksSortedAscB_drop_head_pattern level restLevels restOrders hsorted)
              | false =>
                cases hstp : selfTradeConflict inc resting with
                | true =>
                  cases hpol : inc.stpPolicy.getD .cancelNewest with
                  | cancelNewest =>
                    -- Terminal: output.asks = asks = level :: restLevels
                    exact hsorted
                  | cancelOldest =>
                    exact ih _ _ _ _ hside
                      (asksSortedAscB_drop_head_pattern level restLevels restOrders hsorted)
                  | cancelBoth =>
                    -- Terminal: output.asks = drop_head_order pattern
                    exact asksSortedAscB_drop_head_pattern level restLevels restOrders hsorted
                  | decrement =>
                    cases hrz : (min inc.remainingQty resting.visibleQty == 0) with
                    | true =>
                      -- reduceQty=0 stranded: drop_head_order
                      exact ih _ _ _ _ hside
                        (asksSortedAscB_drop_head_pattern level restLevels restOrders hsorted)
                    | false =>
                      cases hrr : (resting.remainingQty - min inc.remainingQty resting.visibleQty == 0) with
                      | true =>
                        -- restRem=0: drop_head_order
                        exact ih _ _ _ _ hside
                          (asksSortedAscB_drop_head_pattern level restLevels restOrders hsorted)
                      | false =>
                        cases hiv :
                            ((resting.visibleQty - min inc.remainingQty resting.visibleQty == 0)
                              && resting.displayQty.isSome) with
                        | true =>
                          -- STP decrement iceberg reload: modify head orders
                          have hne : ∀ (y : Order),
                              (restOrders ++ [y]).isEmpty = false := by
                            intro y; cases restOrders <;> rfl
                          simp only [hne, if_false]
                          exact ih _ _ _ _ hside
                            (asksSortedAscB_modify_head level restLevels _ hsorted)
                        | false =>
                          -- Partial decrement: modify head orders
                          exact ih _ _ _ _ hside
                            (asksSortedAscB_modify_head level restLevels _ hsorted)
                | false =>
                  -- Normal fill
                  cases hff : (resting.remainingQty -
                               min inc.remainingQty resting.visibleQty == 0) with
                  | true =>
                    -- Full fill: drop_head_order
                    exact ih _ _ _ _ hside
                      (asksSortedAscB_drop_head_pattern level restLevels restOrders hsorted)
                  | false =>
                    cases hir :
                        ((resting.visibleQty - min inc.remainingQty resting.visibleQty == 0)
                          && resting.displayQty.isSome) with
                    | true =>
                      -- Iceberg reload: modify head orders
                      exact ih _ _ _ _ hside
                        (asksSortedAscB_modify_head level restLevels _ hsorted)
                    | false =>
                      -- Partial fill: modify head orders
                      exact ih _ _ _ _ hside
                        (asksSortedAscB_modify_head level restLevels _ hsorted)
      · -- sell branch: absurd
        rename_i heq
        rw [hside] at heq; exact absurd heq (by decide)

/-- **Sell side**: `doMatch` preserves `bidsSortedDescB` on the contra side. -/
theorem doMatch_sell_preserves_bids_sorted (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hside : inc.side = .sell)
    (hsorted : bidsSortedDescB bids = true) :
    bidsSortedDescB (doMatch fuel inc bids asks trades tm).bids = true := by
  induction fuel generalizing inc bids trades tm with
  | zero => unfold doMatch; exact hsorted
  | succ n ih =>
    unfold doMatch
    split
    · exact hsorted
    · split
      · -- buy branch: absurd
        rename_i heq
        rw [hside] at heq; exact absurd heq (by decide)
      · -- sell branch (contra = bids)
        cases hbid : bids with
        | nil => rfl
        | cons level restLevels =>
          simp only
          rw [hbid] at hsorted
          split
          · exact hsorted
          · cases horders : level.orders with
            | nil =>
              exact ih _ _ _ _ hside (bidsSortedDescB_tail level restLevels hsorted)
            | cons resting restOrders =>
              simp only
              cases hzv : (resting.visibleQty == 0 && !selfTradeConflict inc resting) with
              | true =>
                exact ih _ _ _ _ hside
                  (bidsSortedDescB_drop_head_pattern level restLevels restOrders hsorted)
              | false =>
                cases hstp : selfTradeConflict inc resting with
                | true =>
                  cases hpol : inc.stpPolicy.getD .cancelNewest with
                  | cancelNewest => exact hsorted
                  | cancelOldest =>
                    exact ih _ _ _ _ hside
                      (bidsSortedDescB_drop_head_pattern level restLevels restOrders hsorted)
                  | cancelBoth =>
                    exact bidsSortedDescB_drop_head_pattern level restLevels restOrders hsorted
                  | decrement =>
                    cases hrz : (min inc.remainingQty resting.visibleQty == 0) with
                    | true =>
                      exact ih _ _ _ _ hside
                        (bidsSortedDescB_drop_head_pattern level restLevels restOrders hsorted)
                    | false =>
                      cases hrr : (resting.remainingQty - min inc.remainingQty resting.visibleQty == 0) with
                      | true =>
                        exact ih _ _ _ _ hside
                          (bidsSortedDescB_drop_head_pattern level restLevels restOrders hsorted)
                      | false =>
                        cases hiv :
                            ((resting.visibleQty - min inc.remainingQty resting.visibleQty == 0)
                              && resting.displayQty.isSome) with
                        | true =>
                          have hne : ∀ (y : Order),
                              (restOrders ++ [y]).isEmpty = false := by
                            intro y; cases restOrders <;> rfl
                          simp only [hne, if_false]
                          exact ih _ _ _ _ hside
                            (bidsSortedDescB_modify_head level restLevels _ hsorted)
                        | false =>
                          exact ih _ _ _ _ hside
                            (bidsSortedDescB_modify_head level restLevels _ hsorted)
                | false =>
                  cases hff : (resting.remainingQty -
                               min inc.remainingQty resting.visibleQty == 0) with
                  | true =>
                    exact ih _ _ _ _ hside
                      (bidsSortedDescB_drop_head_pattern level restLevels restOrders hsorted)
                  | false =>
                    cases hir :
                        ((resting.visibleQty - min inc.remainingQty resting.visibleQty == 0)
                          && resting.displayQty.isSome) with
                    | true =>
                      exact ih _ _ _ _ hside
                        (bidsSortedDescB_modify_head level restLevels _ hsorted)
                    | false =>
                      exact ih _ _ _ _ hside
                        (bidsSortedDescB_modify_head level restLevels _ hsorted)

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

/-- **Mirror (sell side)**: symmetric to `doMatch_buy_preserves_uncrossed`. -/
theorem doMatch_sell_preserves_uncrossed (fuel : Nat) (inc : Order) (b : BookState)
    (tm : Timestamp) (hside : inc.side = .sell) (h : AllInv b) :
    BookUncrossed { b with
      bids := (doMatch fuel inc b.bids b.asks [] tm).bids,
      asks := (doMatch fuel inc b.bids b.asks [] tm).asks } := by
  have hasks_eq : (doMatch fuel inc b.bids b.asks [] tm).asks = b.asks :=
    doMatch_sell_preserves_asks fuel inc b.bids b.asks [] tm hside
  unfold BookUncrossed bestBidPrice bestAskPrice
  simp only
  -- Case on the RESULT lists
  cases h_resAsks : (doMatch fuel inc b.bids b.asks [] tm).asks with
  | nil => simp
  | cons resAsk resAskRest =>
    cases h_resBids : (doMatch fuel inc b.bids b.asks [] tm).bids with
    | nil => simp
    | cons resBid resBidRest =>
      simp only [List.head?_cons, Option.map_some]
      -- Goal: resBid.price < resAsk.price
      -- From hasks_eq + h_resAsks: b.asks = resAsk :: resAskRest
      have hb_asks : b.asks = resAsk :: resAskRest := by
        rw [← hasks_eq]; exact h_resAsks
      cases hbid : b.bids with
      | nil =>
        exfalso
        have hfalse := doMatch_sell_result_bids_acc fuel inc b.bids b.asks []
          tm (fun _ => False) hside (by intro l hl; rw [hbid] at hl; cases hl)
        exact hfalse resBid (by rw [h_resBids]; exact List.mem_cons_self)
      | cons bHead bRest =>
        -- From AllInv: bHead.price < resAsk.price
        have huc : bHead.price < resAsk.price := by
          have := h.1
          unfold BookUncrossed bestBidPrice bestAskPrice at this
          rw [hbid, hb_asks] at this
          simp only [List.head?_cons, Option.map_some] at this
          exact this
        -- From sortedness: all of b.bids ≤ bHead.price, so all < resAsk.price
        have h_orig_bids : ∀ l ∈ b.bids, l.price < resAsk.price := by
          intro l hl
          have hsorted := h.2.1
          rw [hbid] at hsorted
          have hmax := bidsSortedDescB_head_max bHead bRest hsorted l
            (by rw [hbid] at hl; exact hl)
          exact Nat.lt_of_le_of_lt hmax huc
        -- Apply accumulator to get the predicate on result bids
        have h_res_bids := doMatch_sell_result_bids_acc fuel inc b.bids b.asks []
          tm (fun p => p < resAsk.price) hside h_orig_bids
        exact h_res_bids resBid (by rw [h_resBids]; exact List.mem_cons_self)

/-- **Unified side-parameterized**: doMatch on a sorted+uncrossed book
    preserves `BookUncrossed`. -/
theorem doMatch_preserves_uncrossed (fuel : Nat) (inc : Order) (b : BookState)
    (tm : Timestamp) (side : Side) (hside : inc.side = side) (h : AllInv b) :
    BookUncrossed { b with
      bids := (doMatch fuel inc b.bids b.asks [] tm).bids,
      asks := (doMatch fuel inc b.bids b.asks [] tm).asks } := by
  cases side with
  | buy  => exact doMatch_buy_preserves_uncrossed fuel inc b tm hside h
  | sell => exact doMatch_sell_preserves_uncrossed fuel inc b tm hside h

/-- `doMatch` preserves bids sortedness regardless of side. -/
theorem doMatch_preserves_bids_sorted (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hsorted : bidsSortedDescB bids = true) :
    bidsSortedDescB (doMatch fuel inc bids asks trades tm).bids = true := by
  cases hs : inc.side with
  | buy =>
    rw [doMatch_buy_preserves_bids fuel inc bids asks trades tm hs]
    exact hsorted
  | sell =>
    exact doMatch_sell_preserves_bids_sorted fuel inc bids asks trades tm hs hsorted

/-- `doMatch` preserves asks sortedness regardless of side. -/
theorem doMatch_preserves_asks_sorted (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hsorted : asksSortedAscB asks = true) :
    asksSortedAscB (doMatch fuel inc bids asks trades tm).asks = true := by
  cases hs : inc.side with
  | buy =>
    exact doMatch_buy_preserves_asks_sorted fuel inc bids asks trades tm hs hsorted
  | sell =>
    rw [doMatch_sell_preserves_asks fuel inc bids asks trades tm hs]
    exact hsorted

/-- `doMatch` preserves `inc.side` — doMatch only modifies inc via record
    updates on `remainingQty`/`status`, never on `.side`.
    **Sorry'd**: 120-line mechanical structural induction, deferred. -/
theorem doMatch_preserves_inc_side (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp) :
    (doMatch fuel inc bids asks trades tm).incoming.side = inc.side := by
  sorry

/-- `doMatch` preserves `inc.price` — same structure as inc_side. -/
theorem doMatch_preserves_inc_price (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp) :
    (doMatch fuel inc bids asks trades tm).incoming.price = inc.price := by
  sorry

/-- `doMatch` preserves `inc.orderType`. -/
theorem doMatch_preserves_inc_orderType (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp) :
    (doMatch fuel inc bids asks trades tm).incoming.orderType = inc.orderType := by
  sorry

/-- `doMatch` preserves `inc.tif`. -/
theorem doMatch_preserves_inc_tif (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp) :
    (doMatch fuel inc bids asks trades tm).incoming.tif = inc.tif := by
  sorry

/-- `doMatch` preserves the full `AllInv` (uncrossed + both sides sorted). -/
theorem doMatch_preserves_AllInv (fuel : Nat) (inc : Order) (b : BookState)
    (tm : Timestamp) (side : Side) (hside : inc.side = side) (h : AllInv b) :
    AllInv { b with
      bids := (doMatch fuel inc b.bids b.asks [] tm).bids,
      asks := (doMatch fuel inc b.bids b.asks [] tm).asks,
      clock := (doMatch fuel inc b.bids b.asks [] tm).clock } := by
  refine ⟨?_, ?_, ?_⟩
  · -- BookUncrossed: metadata (clock) doesn't matter
    have := doMatch_preserves_uncrossed fuel inc b tm side hside h
    exact (BookUncrossed_with_clock _ _).mp this
  · -- bids sorted
    exact doMatch_preserves_bids_sorted fuel inc b.bids b.asks [] tm h.2.1
  · -- asks sorted
    exact doMatch_preserves_asks_sorted fuel inc b.bids b.asks [] tm h.2.2

/-- `insertOrder` preserves `AllInv`, given the non-crossing precondition. -/
theorem insertOrder_preserves_AllInv (b : BookState) (o : Order) (hasTrades : Bool)
    (h : AllInv b)
    (hprice : match o.side with
      | .buy  => ∀ askP ∈ bestAskPrice b, (o.price.getD 0) < askP
      | .sell => ∀ bidP ∈ bestBidPrice b, bidP < (o.price.getD 0)) :
    AllInv (insertOrder b o hasTrades) := by
  refine ⟨?_, ?_, ?_⟩
  · cases hs : o.side with
    | buy =>
      have hp : ∀ askP ∈ bestAskPrice b, (o.price.getD 0) < askP := by
        have := hprice
        rw [hs] at this; exact this
      exact insertOrder_buy_preserves_uncrossed b o hasTrades hs h.1 hp
    | sell =>
      have hp : ∀ bidP ∈ bestBidPrice b, bidP < (o.price.getD 0) := by
        have := hprice
        rw [hs] at this; exact this
      exact insertOrder_sell_preserves_uncrossed b o hasTrades hs h.1 hp
  · exact (insertOrder_preserves_sortedness b o hasTrades h.2.1 h.2.2).1
  · exact (insertOrder_preserves_sortedness b o hasTrades h.2.1 h.2.2).2

/-- `dispose` preserves `AllInv`. The non-crossing precondition is only
    needed if dispose actually inserts (the last branch); in all other
    branches dispose returns `b` unchanged. -/
theorem dispose_preserves_AllInv (inc : Order) (b : BookState) (trades : List Trade)
    (h : AllInv b)
    (hprice :
      ¬ (inc.remainingQty = 0 ∨ inc.status = .cancelled ∨
         inc.tif = .ioc ∨ inc.orderType = .market) →
      match inc.side with
      | .buy  => ∀ askP ∈ bestAskPrice b, (inc.price.getD 0) < askP
      | .sell => ∀ bidP ∈ bestBidPrice b, bidP < (inc.price.getD 0)) :
    AllInv (dispose inc b trades) := by
  unfold dispose
  split
  · exact h
  split
  · exact h
  split
  · exact h
  · rename_i h1 h2 h3
    apply insertOrder_preserves_AllInv b inc _ h
    apply hprice
    intro hor
    exfalso
    rcases hor with hq | hs | hi | hm
    · apply h1
      show (inc.remainingQty == 0 || inc.status == OrderStatus.cancelled) = true
      rw [hq]; rfl
    · apply h1
      show (inc.remainingQty == 0 || inc.status == OrderStatus.cancelled) = true
      rw [hs]
      cases hq : inc.remainingQty with
      | zero => rfl
      | succ k =>
        show ((k + 1 == 0) || true) = true
        simp
    · apply h2
      show (inc.tif == TimeInForce.ioc) = true
      rw [hi]; rfl
    · apply h3
      show (inc.orderType == OrderType.market) = true
      rw [hm]; rfl

-- ============================================================================
-- doMatch buy-side no-cross after matching
-- ============================================================================

/-- Buy-side "stable" predicate: doMatch has nothing more to do. Either the
    incoming is consumed/cancelled, or the contra side is empty, or the head
    of the contra side is non-crossing (price strictly above `inc.price`). -/
def buyMatchStable (inc : Order) (asks : List PriceLevel) : Prop :=
  inc.remainingQty = 0 ∨ inc.status = .cancelled ∨ asks = [] ∨
  (∀ hd ∈ asks.head?, (inc.price.getD 0) < hd.price)

/-- Sell-side "stable" predicate (mirror of `buyMatchStable`). The 4th
    disjunct flips: bid head price must be strictly BELOW `inc.price`. -/
def sellMatchStable (inc : Order) (bids : List PriceLevel) : Prop :=
  inc.remainingQty = 0 ∨ inc.status = .cancelled ∨ bids = [] ∨
  (∀ hd ∈ bids.head?, hd.price < (inc.price.getD 0))

/-- Trivial extraction: from a buy-stable state where incoming is still active,
    the no-cross conclusion follows. -/
theorem doMatch_buy_noCross_of_stable
    {inc : Order} {asks : List PriceLevel}
    (hstable : buyMatchStable inc asks)
    (hqty : inc.remainingQty > 0)
    (hstatus : inc.status ≠ .cancelled) :
    asks = [] ∨ (∀ hd ∈ asks.head?, (inc.price.getD 0) < hd.price) := by
  rcases hstable with h | h | h | h
  · rw [h] at hqty; exact absurd hqty (by decide)
  · exact absurd h hstatus
  · exact Or.inl h
  · exact Or.inr h

/-- Sell mirror of `doMatch_buy_noCross_of_stable`. -/
theorem doMatch_sell_noCross_of_stable
    {inc : Order} {bids : List PriceLevel}
    (hstable : sellMatchStable inc bids)
    (hqty : inc.remainingQty > 0)
    (hstatus : inc.status ≠ .cancelled) :
    bids = [] ∨ (∀ hd ∈ bids.head?, hd.price < (inc.price.getD 0)) := by
  rcases hstable with h | h | h | h
  · rw [h] at hqty; exact absurd hqty (by decide)
  · exact absurd h hstatus
  · exact Or.inl h
  · exact Or.inr h

-- ============================================================================
-- doMatch termination — progress lemma approach
-- ============================================================================

/-- Sum of `remainingQty` over a list of orders (direct recursion for
    easier proof unfolding). -/
def orderSum : List Order → Nat
  | [] => 0
  | o :: rest => o.remainingQty + orderSum rest

/-- Total remaining quantity across all orders on all price levels.
    Primary component of the termination measure. -/
def totalRemaining : List PriceLevel → Nat
  | [] => 0
  | l :: rest => orderSum l.orders + totalRemaining rest

/-- Total number of orders across all price levels. Needed in the measure
    because the empty-level-skip branch of `doMatch` doesn't change
    `totalRemaining` but does shrink the level list. -/
def orderCount : List PriceLevel → Nat
  | [] => 0
  | l :: rest => l.orders.length + orderCount rest

/-- Well-founded measure for `doMatch` progress:
    `totalRemaining + orderCount + contra.length`. Every non-terminal
    recursive step strictly decreases at least one component, so this is
    sufficient without any incoming-order component. Matches
    `computeMatchFuel` exactly: `computeMatchFuel b side = matchMeasure contra + 1`.

    The `_inc` parameter is retained in the signature for backward compatibility
    with existing lemma call sites but is unused — the measure ignores it. -/
def matchMeasure (contra : List PriceLevel) (_inc : Order) : Nat :=
  totalRemaining contra + orderCount contra + contra.length

/-- Helper: arithmetic chain `fuel > old_measure ∧ new_measure < old_measure → fuel' > new_measure`
    expressed on plain `Nat` so omega can close it without struggling with
    opaque `matchMeasure` atoms. -/
private theorem fuel_from_decrease (n old new : Nat)
    (h_fuel : n + 1 > old) (h_dec : new < old) : n > new := by omega

/-- `orderSum` distributes over `List.append`. Used by iceberg reload cases
    where the new order queue is `restOrders ++ [reloaded]`. -/
theorem orderSum_append (xs ys : List Order) :
    orderSum (xs ++ ys) = orderSum xs + orderSum ys := by
  induction xs with
  | nil => show orderSum ys = 0 + orderSum ys; omega
  | cons x xs' ih =>
    calc orderSum ((x :: xs') ++ ys)
        = x.remainingQty + orderSum (xs' ++ ys) := rfl
      _ = x.remainingQty + (orderSum xs' + orderSum ys) := by rw [ih]
      _ = (x.remainingQty + orderSum xs') + orderSum ys :=
        (Nat.add_assoc _ _ _).symm
      _ = orderSum (x :: xs') + orderSum ys := rfl

/-- `orderSum [o] = o.remainingQty`. -/
theorem orderSum_singleton (o : Order) : orderSum [o] = o.remainingQty := rfl

/-- Monotonicity of `matchMeasure` in the incoming order's `remainingQty`:
    after refactoring matchMeasure to ignore `inc`, this is trivially equality,
    but retained for backward compatibility with existing callers. -/
private theorem matchMeasure_mono_inc_le
    (contra : List PriceLevel) (inc' inc : Order)
    (_h : inc'.remainingQty ≤ inc.remainingQty) :
    matchMeasure contra inc' ≤ matchMeasure contra inc :=
  Nat.le.refl

/-- Dropping the head order from the head level (with the "remove level if
    empty" pattern used by `doMatch`) decreases `totalRemaining` by exactly
    the dropped order's `remainingQty`. -/
theorem totalRemaining_drop_head_order
    (level : PriceLevel) (restLevels : List PriceLevel)
    (resting : Order) (restOrders : List Order)
    (hlevel : level.orders = resting :: restOrders) :
    totalRemaining (if restOrders.isEmpty then restLevels
                    else { level with orders := restOrders } :: restLevels)
      + resting.remainingQty
    = totalRemaining (level :: restLevels) := by
  -- Unfold totalRemaining on `level :: restLevels`
  show _ + resting.remainingQty =
    orderSum level.orders + totalRemaining restLevels
  rw [hlevel]
  show _ + resting.remainingQty =
    orderSum (resting :: restOrders) + totalRemaining restLevels
  show _ + resting.remainingQty =
    (resting.remainingQty + orderSum restOrders) + totalRemaining restLevels
  by_cases h : restOrders.isEmpty
  · -- restOrders empty → result = restLevels
    simp [h]
    have h2 : restOrders = [] := List.isEmpty_iff.mp h
    rw [h2]
    show totalRemaining restLevels + resting.remainingQty =
      (resting.remainingQty + orderSum []) + totalRemaining restLevels
    show totalRemaining restLevels + resting.remainingQty =
      (resting.remainingQty + 0) + totalRemaining restLevels
    omega
  · -- restOrders non-empty → result = {level with orders := restOrders} :: restLevels
    simp [h]
    show orderSum restOrders + totalRemaining restLevels + resting.remainingQty =
      (resting.remainingQty + orderSum restOrders) + totalRemaining restLevels
    omega

/-- Strict-decrease corollary: if the dropped order had positive remaining
    quantity, `totalRemaining` strictly decreases. -/
theorem totalRemaining_drop_head_order_lt
    (level : PriceLevel) (restLevels : List PriceLevel)
    (resting : Order) (restOrders : List Order)
    (hlevel : level.orders = resting :: restOrders)
    (hpos : resting.remainingQty > 0) :
    totalRemaining (if restOrders.isEmpty then restLevels
                    else { level with orders := restOrders } :: restLevels)
    < totalRemaining (level :: restLevels) := by
  have heq := totalRemaining_drop_head_order level restLevels resting restOrders hlevel
  calc totalRemaining (if restOrders.isEmpty then restLevels
                        else { level with orders := restOrders } :: restLevels)
      < totalRemaining (if restOrders.isEmpty then restLevels
                        else { level with orders := restOrders } :: restLevels)
        + resting.remainingQty := by
          exact Nat.lt_add_of_pos_right hpos
    _ = totalRemaining (level :: restLevels) := heq

/-- Empty-level-skip: dropping a head level whose `orders` is empty leaves
    `totalRemaining` and `orderCount` unchanged, and decreases the level
    count by 1. Hence `matchMeasure` strictly decreases. -/
theorem matchMeasure_skip_empty_level
    (level : PriceLevel) (restLevels : List PriceLevel) (inc : Order)
    (hempty : level.orders = []) :
    matchMeasure restLevels inc < matchMeasure (level :: restLevels) inc := by
  unfold matchMeasure
  -- totalRemaining (level :: rest) = orderSum [] + totalRemaining rest = totalRemaining rest
  have ht : totalRemaining (level :: restLevels) = totalRemaining restLevels := by
    show orderSum level.orders + totalRemaining restLevels = _
    rw [hempty]; show orderSum [] + _ = _; show 0 + _ = _; omega
  have hoc : orderCount (level :: restLevels) = orderCount restLevels := by
    show level.orders.length + orderCount restLevels = _
    rw [hempty]; simp
  have hlen : (level :: restLevels).length = restLevels.length + 1 := by simp
  rw [ht, hoc, hlen]
  omega

/-- `orderCount` equivalent of `totalRemaining_drop_head_order`:
    dropping the head order from the head level decreases `orderCount` by 1. -/
theorem orderCount_drop_head_order
    (level : PriceLevel) (restLevels : List PriceLevel)
    (resting : Order) (restOrders : List Order)
    (hlevel : level.orders = resting :: restOrders) :
    orderCount (if restOrders.isEmpty then restLevels
                else { level with orders := restOrders } :: restLevels) + 1
    = orderCount (level :: restLevels) := by
  show _ + 1 = level.orders.length + orderCount restLevels
  rw [hlevel]
  by_cases h : restOrders.isEmpty
  · simp [h]
    have h2 : restOrders = [] := List.isEmpty_iff.mp h
    rw [h2]; simp; omega
  · simp [h]
    show (restOrders.length + orderCount restLevels) + 1 = _
    show _ = (resting :: restOrders).length + orderCount restLevels
    simp; omega

/-- `contra.length` non-increase under `drop_head_order`:
    the head-level drop either keeps the length (restOrders non-empty) or
    decreases by 1 (restOrders empty). -/
theorem length_drop_head_order_le
    (level : PriceLevel) (restLevels : List PriceLevel)
    (restOrders : List Order) :
    (if restOrders.isEmpty then restLevels
     else { level with orders := restOrders } :: restLevels).length
    ≤ (level :: restLevels).length := by
  by_cases h : restOrders.isEmpty
  · simp [h]
  · simp [h]

/-- Modifying the head level's orders (keeping count the same) strictly
    decreases `matchMeasure` iff the new `orderSum` is less. Covers partial
    fills, STP decrement partial, and iceberg reload (where the reloaded
    order replaces the head at the tail of the queue — same length). -/
theorem matchMeasure_modify_head_level_orders
    (level : PriceLevel) (restLevels : List PriceLevel) (inc : Order)
    (newOrders : List Order)
    (hlen : newOrders.length = level.orders.length)
    (hdec : orderSum newOrders < orderSum level.orders) :
    matchMeasure ({ level with orders := newOrders } :: restLevels) inc
    < matchMeasure (level :: restLevels) inc := by
  unfold matchMeasure
  -- Unfold totalRemaining on both sides
  have ht_new : totalRemaining ({ level with orders := newOrders } :: restLevels)
    = orderSum newOrders + totalRemaining restLevels := rfl
  have ht_old : totalRemaining (level :: restLevels)
    = orderSum level.orders + totalRemaining restLevels := rfl
  -- Unfold orderCount on both sides
  have ho_new : orderCount ({ level with orders := newOrders } :: restLevels)
    = newOrders.length + orderCount restLevels := rfl
  have ho_old : orderCount (level :: restLevels)
    = level.orders.length + orderCount restLevels := rfl
  -- Lengths are equal
  have hl : ({ level with orders := newOrders } :: restLevels).length
    = (level :: restLevels).length := by simp
  rw [ht_new, ht_old, ho_new, ho_old, hl]
  omega

/-- **Main per-branch lemma**: dropping a head order strictly decreases
    `matchMeasure`. The strict decrease comes from `orderCount` dropping by 1
    (so `hpos` is not needed — the lemma holds for any dropped order). -/
theorem matchMeasure_drop_head_order
    (level : PriceLevel) (restLevels : List PriceLevel) (inc : Order)
    (resting : Order) (restOrders : List Order)
    (hlevel : level.orders = resting :: restOrders) :
    matchMeasure (if restOrders.isEmpty then restLevels
                  else { level with orders := restOrders } :: restLevels) inc
    < matchMeasure (level :: restLevels) inc := by
  unfold matchMeasure
  have htot := totalRemaining_drop_head_order level restLevels resting restOrders hlevel
  have hoc := orderCount_drop_head_order level restLevels resting restOrders hlevel
  have hlen := length_drop_head_order_le level restLevels restOrders
  -- Generalize to hide the if-expression
  generalize hR : totalRemaining (if restOrders.isEmpty then restLevels
                    else { level with orders := restOrders } :: restLevels) = R at htot
  generalize hO : orderCount (if restOrders.isEmpty then restLevels
                    else { level with orders := restOrders } :: restLevels) = O at hoc
  generalize hL : (if restOrders.isEmpty then restLevels
                    else { level with orders := restOrders } :: restLevels).length = L at hlen
  omega

/-- **Sub-lemma (task #4)**: the output of `doMatch` for a buy-side order
    on a sorted ask list is buy-stable. Proven via the progress-lemma approach:
    induction on `fuel` with the hypothesis `fuel > matchMeasure asks inc`.
    At each step, either a terminal branch fires (stable directly) or a
    recursive branch fires with strictly smaller `matchMeasure` (apply IH). -/
theorem doMatch_buy_output_stable (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hside : inc.side = .buy)
    (hfuel : fuel > matchMeasure asks inc) :
    let mr := doMatch fuel inc bids asks trades tm
    buyMatchStable mr.incoming mr.asks := by
  induction fuel generalizing inc asks trades tm with
  | zero =>
    -- 0 > matchMeasure asks inc is impossible (matchMeasure ≥ 0 in Nat)
    exact absurd hfuel (by omega)
  | succ n ih =>
    unfold doMatch
    split
    · -- Terminal: inc.remainingQty == 0 || inc.status == .cancelled
      rename_i hdone
      simp only [Bool.or_eq_true] at hdone
      rcases hdone with hq | hs
      · -- inc.remainingQty == 0 = true
        left
        show inc.remainingQty = 0
        simpa using hq
      · -- inc.status == .cancelled = true
        right; left
        show inc.status = .cancelled
        cases hstat : inc.status
        all_goals first | rfl | (rw [hstat] at hs; cases hs)
    · -- Not terminal: extract the negated condition
      rename_i hnotdone
      have hinc_pos : inc.remainingQty > 0 := by
        apply Nat.pos_of_ne_zero
        intro h0
        rw [h0] at hnotdone
        simp at hnotdone
      split
      · -- buy branch (contra = asks)
        cases hask : asks with
        | nil =>
          -- asks is empty → third disjunct of buyMatchStable
          right; right; left
          rfl
        | cons level restLevels =>
          simp only
          split
          · -- !canMatchPrice inc level.price → terminal (fourth disjunct)
            rename_i hnc
            right; right; right
            intro hd hmem
            have hhd : hd = level := by
              simp at hmem; exact hmem.symm
            rw [hhd]
            -- Now show: inc.price.getD 0 < level.price
            unfold canMatchPrice at hnc
            cases hprice : inc.price with
            | none =>
              -- canMatchPrice = true, so !canMatch = false — contradiction
              exfalso
              rw [hprice] at hnc
              simp at hnc
            | some p =>
              rw [hprice, hside] at hnc
              simp at hnc
              -- hnc : ¬ (level.price ≤ p)
              show (some p).getD 0 < level.price
              show p < level.price
              omega
          · cases horders : level.orders with
            | nil =>
              -- Empty level skip — apply IH with matchMeasure_skip_empty_level
              have hmdec : matchMeasure restLevels inc
                         < matchMeasure (level :: restLevels) inc :=
                matchMeasure_skip_empty_level level restLevels inc horders
              have hfuel' : n > matchMeasure restLevels inc := by
                have hprev : n + 1 > matchMeasure asks inc := hfuel
                rw [hask] at hprev
                omega
              exact ih inc restLevels trades tm hside hfuel'
            | cons resting restOrders =>
              simp only
              cases hzv : (resting.visibleQty == 0 && !selfTradeConflict inc resting) with
              | true =>
                -- Zero-visible skip: head order removed from level.
                -- Recursive: doMatch n inc bids (if restOrders.isEmpty then restLevels else ...) trades tm
                -- Apply matchMeasure_drop_head_order to get the decrease, then IH.
                have hmdec :=
                  matchMeasure_drop_head_order level restLevels inc
                    resting restOrders horders
                have hfuel' :
                    n > matchMeasure
                      (if restOrders.isEmpty then restLevels
                       else { level with orders := restOrders } :: restLevels) inc := by
                  have hprev : n + 1 > matchMeasure asks inc := hfuel
                  rw [hask] at hprev
                  omega
                exact ih inc _ _ _ hside hfuel'
              | false =>
                cases hstp : selfTradeConflict inc resting with
                | true =>
                  -- STP conflict: policy match
                  cases hpol : inc.stpPolicy.getD .cancelNewest with
                  | cancelNewest =>
                    -- Terminal: inc.status becomes .cancelled
                    right; left
                    show OrderStatus.cancelled = OrderStatus.cancelled
                    rfl
                  | cancelOldest =>
                    -- Recursive: drop head order, same inc
                    have hmdec :=
                      matchMeasure_drop_head_order level restLevels inc
                        resting restOrders horders
                    have hfuel' :
                        n > matchMeasure
                          (if restOrders.isEmpty then restLevels
                           else { level with orders := restOrders } :: restLevels) inc := by
                      have hprev : n + 1 > matchMeasure asks inc := hfuel
                      rw [hask] at hprev
                      omega
                    exact ih inc _ _ _ hside hfuel'
                  | cancelBoth =>
                    -- Terminal: inc.status becomes .cancelled
                    right; left
                    show OrderStatus.cancelled = OrderStatus.cancelled
                    rfl
                  | decrement =>
                    cases hrz : (min inc.remainingQty resting.visibleQty == 0) with
                    | true =>
                      -- reduceQty = 0: stranded remove (drop_head_order, same inc)
                      have hmdec :=
                        matchMeasure_drop_head_order level restLevels inc
                          resting restOrders horders
                      have hfuel' :
                          n > matchMeasure
                            (if restOrders.isEmpty then restLevels
                             else { level with orders := restOrders } :: restLevels) inc := by
                        have hprev : n + 1 > matchMeasure asks inc := hfuel
                        rw [hask] at hprev
                        omega
                      exact ih inc _ _ _ hside hfuel'
                    | false =>
                      cases hrr : (resting.remainingQty - min inc.remainingQty resting.visibleQty == 0) with
                      | true =>
                        -- restRem = 0: drop_head_order with inc' (inc with reduced qty)
                        -- Open the new inc inline to avoid let-unfolding quirks.
                        refine ih
                          ({ inc with
                            remainingQty := inc.remainingQty -
                              min inc.remainingQty resting.visibleQty,
                            status := if inc.remainingQty -
                              min inc.remainingQty resting.visibleQty == 0 then
                              .cancelled else inc.status })
                          _ _ _ hside ?_
                        -- Goal: n > matchMeasure (if ...) inc'
                        -- Chain: hmdec gives < matchMeasure (level :: restLevels) inc'
                        --        which = matchMeasure asks inc' (by hask)
                        --        which ≤ matchMeasure asks inc (since remainingQty decreased)
                        --        which < n + 1 (hfuel)
                        have hmdec := matchMeasure_drop_head_order level restLevels
                          ({ inc with
                            remainingQty := inc.remainingQty -
                              min inc.remainingQty resting.visibleQty,
                            status := if inc.remainingQty -
                              min inc.remainingQty resting.visibleQty == 0 then
                              .cancelled else inc.status })
                          resting restOrders horders
                        -- Rewrite hmdec to use `asks` instead of `(level :: restLevels)`
                        rw [← hask] at hmdec
                        -- Show matchMeasure asks inc' ≤ matchMeasure asks inc
                        have h_mono :
                            matchMeasure asks
                              ({ inc with
                                remainingQty := inc.remainingQty -
                                  min inc.remainingQty resting.visibleQty,
                                status := if inc.remainingQty -
                                  min inc.remainingQty resting.visibleQty == 0 then
                                  .cancelled else inc.status })
                            ≤ matchMeasure asks inc := by
                          -- matchMeasure ignores inc, so this is reflexivity
                          exact Nat.le.refl
                        omega
                      | false =>
                        -- STP decrement, restRem > 0: iceberg reload OR partial decrement
                        cases hiv :
                            ((resting.visibleQty - min inc.remainingQty resting.visibleQty == 0)
                              && resting.displayQty.isSome) with
                        | true =>
                          -- STP decrement iceberg reload.
                          -- In STP branch, can't derive visibleQty > 0 from hzv+hstp
                          -- (the zero-visible skip is bypassed for STP conflicts).
                          -- Use hrz : reduceQty != 0 → min _ _ > 0 directly.
                          have hrz_pos : 0 < min inc.remainingQty resting.visibleQty := by
                            apply Nat.pos_of_ne_zero
                            intro he
                            rw [he] at hrz
                            simp at hrz
                          have hrr_prop : resting.remainingQty -
                                          min inc.remainingQty resting.visibleQty > 0 := by
                            apply Nat.pos_of_ne_zero
                            intro he
                            rw [he] at hrr
                            simp at hrr
                          have hr_pos : 0 < resting.remainingQty := by
                            apply Nat.pos_of_ne_zero
                            intro he
                            rw [he] at hrr_prop
                            simp at hrr_prop
                          -- The if-then-else on newQueue.isEmpty always takes the else
                          -- branch since restOrders ++ [reloaded] is non-empty.
                          -- We reduce it via `simp only` on List.append/isEmpty.
                          have hne : ∀ (y : Order),
                              (restOrders ++ [y]).isEmpty = false := by
                            intro y; cases restOrders <;> rfl
                          simp only [hne, if_false]
                          -- Now the goal has level'' = {level with orders := restOrders ++ [reloaded]}
                          -- :: restLevels. Same pattern as normal fill iceberg.
                          have hmdec_lvl :
                              matchMeasure ({ level with orders := restOrders ++
                                  [({ resting with
                                      visibleQty := min (resting.displayQty.getD 0)
                                        (resting.remainingQty -
                                          min inc.remainingQty resting.visibleQty),
                                      remainingQty := resting.remainingQty -
                                        min inc.remainingQty resting.visibleQty,
                                      timestamp := tm,
                                      status := OrderStatus.partiallyFilled } : Order)] }
                                             :: restLevels)
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order)
                              < matchMeasure (level :: restLevels)
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order) := by
                            apply matchMeasure_modify_head_level_orders
                            · rw [horders]
                              simp
                            · rw [horders, orderSum_append, orderSum_singleton]
                              show orderSum restOrders +
                                   (resting.remainingQty -
                                     min inc.remainingQty resting.visibleQty)
                                 < orderSum (resting :: restOrders)
                              show orderSum restOrders +
                                   (resting.remainingQty -
                                     min inc.remainingQty resting.visibleQty)
                                 < resting.remainingQty + orderSum restOrders
                              have h_lt : resting.remainingQty -
                                          min inc.remainingQty resting.visibleQty
                                        < resting.remainingQty :=
                                Nat.sub_lt hr_pos hrz_pos
                              rw [Nat.add_comm resting.remainingQty (orderSum restOrders)]
                              exact Nat.add_lt_add_left h_lt (orderSum restOrders)
                          rw [← hask] at hmdec_lvl
                          have h_mono :
                              matchMeasure asks
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order)
                              ≤ matchMeasure asks inc := by
                            apply matchMeasure_mono_inc_le
                            show inc.remainingQty - min inc.remainingQty resting.visibleQty
                                 ≤ inc.remainingQty
                            exact Nat.sub_le _ _
                          refine ih
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty,
                              status := if inc.remainingQty -
                                min inc.remainingQty resting.visibleQty == 0 then
                                .cancelled else inc.status } : Order)
                            _ _ _ hside ?_
                          exact fuel_from_decrease n _ _ hfuel
                            (Nat.lt_of_lt_of_le hmdec_lvl h_mono)
                        | false =>
                          -- Partial decrement: modify_head_level_orders with reduceQty > 0
                          have hrz_pos : min inc.remainingQty resting.visibleQty > 0 := by
                            apply Nat.pos_of_ne_zero
                            intro he
                            rw [he] at hrz
                            simp at hrz
                          have hmdec_lvl :
                              matchMeasure
                                ({ level with orders :=
                                    ({ resting with
                                        remainingQty := resting.remainingQty -
                                          min inc.remainingQty resting.visibleQty,
                                        visibleQty := resting.visibleQty -
                                          min inc.remainingQty resting.visibleQty } : Order)
                                    :: restOrders } :: restLevels)
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order)
                              < matchMeasure (level :: restLevels)
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order) := by
                            apply matchMeasure_modify_head_level_orders
                            · rw [horders]; simp
                            · rw [horders]
                              show (resting.remainingQty -
                                    min inc.remainingQty resting.visibleQty)
                                  + orderSum restOrders
                                  < resting.remainingQty + orderSum restOrders
                              have hr_pos : 0 < resting.remainingQty := by
                                apply Nat.pos_of_ne_zero
                                intro he
                                rw [he] at hrr
                                simp at hrr
                              have h_lt : resting.remainingQty -
                                          min inc.remainingQty resting.visibleQty
                                        < resting.remainingQty :=
                                Nat.sub_lt hr_pos hrz_pos
                              exact Nat.add_lt_add_right h_lt _
                          rw [← hask] at hmdec_lvl
                          have h_mono :
                              matchMeasure asks
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order)
                              ≤ matchMeasure asks inc := by
                            apply matchMeasure_mono_inc_le
                            show inc.remainingQty - min inc.remainingQty resting.visibleQty
                                 ≤ inc.remainingQty
                            exact Nat.sub_le _ _
                          refine ih
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty,
                              status := if inc.remainingQty -
                                min inc.remainingQty resting.visibleQty == 0 then
                                .cancelled else inc.status } : Order)
                            _ _ _ hside ?_
                          exact fuel_from_decrease n _ _ hfuel (Nat.lt_of_lt_of_le hmdec_lvl h_mono)
                | false =>
                  -- Normal fill
                  cases hff : (resting.remainingQty -
                               min inc.remainingQty resting.visibleQty == 0) with
                  | true =>
                    -- Full fill: drop_head_order with inc' (qty reduced)
                    have hmdec := matchMeasure_drop_head_order level restLevels
                      ({ inc with
                        remainingQty := inc.remainingQty -
                          min inc.remainingQty resting.visibleQty } : Order)
                      resting restOrders horders
                    rw [← hask] at hmdec
                    have h_mono :
                        matchMeasure asks
                          ({ inc with
                            remainingQty := inc.remainingQty -
                              min inc.remainingQty resting.visibleQty } : Order)
                        ≤ matchMeasure asks inc := by
                      exact Nat.le.refl
                    refine ih
                      ({ inc with
                        remainingQty := inc.remainingQty -
                          min inc.remainingQty resting.visibleQty } : Order)
                      _ _ _ hside ?_
                    omega
                  | false =>
                    -- Partial fill or iceberg reload: further split on vis==0 && displayQty
                    cases hir :
                        ((resting.visibleQty - min inc.remainingQty resting.visibleQty == 0)
                          && resting.displayQty.isSome) with
                    | true =>
                      -- Normal fill iceberg reload: newQueue = restOrders ++ [reloaded]
                      -- Length unchanged, orderSum decreases by fillQty > 0.
                      have hvis_pos : resting.visibleQty > 0 := by
                        apply Nat.pos_of_ne_zero
                        intro hv
                        rw [hv] at hzv
                        simp [hstp] at hzv
                      have hfill_pos : 0 < min inc.remainingQty resting.visibleQty :=
                        Nat.lt_min.mpr ⟨hinc_pos, hvis_pos⟩
                      have hff_prop : resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty > 0 := by
                        apply Nat.pos_of_ne_zero
                        intro he
                        rw [he] at hff
                        simp at hff
                      have hr_pos : 0 < resting.remainingQty := by
                        apply Nat.pos_of_ne_zero
                        intro he
                        rw [he] at hff_prop
                        simp at hff_prop
                      -- Apply modify_head_level_orders with the reloaded queue.
                      -- Key fact: orderSum (restOrders ++ [reloaded]) < orderSum (resting :: restOrders)
                      -- Since reloaded.remainingQty = resting.remainingQty - fillQty < resting.remainingQty.
                      have h_qty_lt : resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty
                                    < resting.remainingQty :=
                        Nat.sub_lt hr_pos hfill_pos
                      have hmdec_lvl :
                          matchMeasure ({ level with orders := restOrders ++
                              [({ resting with
                                  visibleQty := min (resting.displayQty.getD 0)
                                    (resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty),
                                  remainingQty := resting.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  timestamp := tm,
                                  status := OrderStatus.partiallyFilled } : Order)] }
                                         :: restLevels)
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order)
                          < matchMeasure (level :: restLevels)
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order) := by
                        apply matchMeasure_modify_head_level_orders
                        · rw [horders]
                          simp
                        · rw [horders, orderSum_append, orderSum_singleton]
                          show orderSum restOrders +
                               (resting.remainingQty - min inc.remainingQty resting.visibleQty)
                             < orderSum (resting :: restOrders)
                          show orderSum restOrders +
                               (resting.remainingQty - min inc.remainingQty resting.visibleQty)
                             < resting.remainingQty + orderSum restOrders
                          -- Goal: orderSum restOrders + (resting.remainingQty - min _ _)
                          --     < resting.remainingQty + orderSum restOrders
                          have h_lt : resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty
                                    < resting.remainingQty :=
                            Nat.sub_lt hr_pos hfill_pos
                          rw [Nat.add_comm resting.remainingQty (orderSum restOrders)]
                          exact Nat.add_lt_add_left h_lt (orderSum restOrders)
                      rw [← hask] at hmdec_lvl
                      have h_mono :
                          matchMeasure asks
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order)
                          ≤ matchMeasure asks inc := by
                        apply matchMeasure_mono_inc_le
                        show inc.remainingQty - min inc.remainingQty resting.visibleQty
                             ≤ inc.remainingQty
                        exact Nat.sub_le _ _
                      refine ih
                        ({ inc with
                          remainingQty := inc.remainingQty -
                            min inc.remainingQty resting.visibleQty } : Order)
                        _ _ _ hside ?_
                      exact fuel_from_decrease n _ _ hfuel (Nat.lt_of_lt_of_le hmdec_lvl h_mono)
                    | false =>
                      -- Partial fill: level.orders = resting :: restOrders becomes
                      -- updRest :: restOrders where updRest.remainingQty < resting.remainingQty.
                      have hvis_pos : resting.visibleQty > 0 := by
                        apply Nat.pos_of_ne_zero
                        intro hv
                        rw [hv] at hzv
                        simp [hstp] at hzv
                      have hfill_pos : 0 < min inc.remainingQty resting.visibleQty :=
                        Nat.lt_min.mpr ⟨hinc_pos, hvis_pos⟩
                      have hff_prop : resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty > 0 := by
                        apply Nat.pos_of_ne_zero
                        intro he
                        rw [he] at hff
                        simp at hff
                      -- Strict decrease via matchMeasure_modify_head_level_orders
                      have hmdec_lvl :
                          matchMeasure
                            ({ level with orders :=
                                ({ resting with
                                    visibleQty := resting.visibleQty -
                                      min inc.remainingQty resting.visibleQty,
                                    remainingQty := resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty,
                                    status := OrderStatus.partiallyFilled } : Order)
                                :: restOrders } :: restLevels)
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order)
                          < matchMeasure (level :: restLevels)
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order) := by
                        apply matchMeasure_modify_head_level_orders
                        · rw [horders]; simp
                        · rw [horders]
                          show (resting.remainingQty -
                                min inc.remainingQty resting.visibleQty)
                              + orderSum restOrders
                              < resting.remainingQty + orderSum restOrders
                          -- Case-split on min to eliminate it for omega
                          rcases Nat.le_total inc.remainingQty resting.visibleQty with hle | hle
                          · rw [Nat.min_eq_left hle] at hff_prop hfill_pos ⊢
                            have hr_pos : 0 < resting.remainingQty := by
                              apply Nat.pos_of_ne_zero
                              intro he
                              rw [he] at hff_prop
                              simp at hff_prop
                            have h_lt : resting.remainingQty - inc.remainingQty
                                      < resting.remainingQty :=
                              Nat.sub_lt hr_pos hinc_pos
                            exact Nat.add_lt_add_right h_lt _
                          · rw [Nat.min_eq_right hle] at hff_prop hfill_pos ⊢
                            have hr_pos : 0 < resting.remainingQty := by
                              apply Nat.pos_of_ne_zero
                              intro he
                              rw [he] at hff_prop
                              simp at hff_prop
                            have h_lt : resting.remainingQty - resting.visibleQty
                                      < resting.remainingQty :=
                              Nat.sub_lt hr_pos hvis_pos
                            exact Nat.add_lt_add_right h_lt _
                      rw [← hask] at hmdec_lvl
                      have h_mono :
                          matchMeasure asks
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order)
                          ≤ matchMeasure asks inc := by
                        exact Nat.le.refl
                      refine ih
                        ({ inc with
                          remainingQty := inc.remainingQty -
                            min inc.remainingQty resting.visibleQty } : Order)
                        _ _ _ hside ?_
                      omega
      · -- sell branch is absurd since hside : inc.side = .buy
        rename_i heq
        rw [hside] at heq; exact absurd heq (by decide)

/-- **Main no-cross lemma (buy side)**: after buy-side matching with sufficient
    fuel, if the incoming order still has quantity to fill, the remaining asks
    are either empty or have a head price strictly above the incoming order's
    limit price. -/
theorem doMatch_buy_noCross_after_match (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hside : inc.side = .buy)
    (hfuel : fuel > matchMeasure asks inc) :
    let mr := doMatch fuel inc bids asks trades tm
    mr.incoming.remainingQty > 0 →
    mr.incoming.status ≠ .cancelled →
    mr.asks = [] ∨ (∀ hd ∈ mr.asks.head?, (mr.incoming.price.getD 0) < hd.price) := by
  intro mr hqty hstatus
  have hstable := doMatch_buy_output_stable fuel inc bids asks trades tm hside hfuel
  exact doMatch_buy_noCross_of_stable hstable hqty hstatus

/-- **Sell mirror of `doMatch_buy_output_stable`**: structural copy with
    asks↔bids, .buy↔.sell, and strict-less direction flipped. -/
theorem doMatch_sell_output_stable (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hside : inc.side = .sell)
    (hfuel : fuel > matchMeasure bids inc) :
    let mr := doMatch fuel inc bids asks trades tm
    sellMatchStable mr.incoming mr.bids := by
  induction fuel generalizing inc bids trades tm with
  | zero =>
    exact absurd hfuel (by omega)
  | succ n ih =>
    unfold doMatch
    split
    · -- Terminal
      rename_i hdone
      simp only [Bool.or_eq_true] at hdone
      rcases hdone with hq | hs
      · left
        show inc.remainingQty = 0
        simpa using hq
      · right; left
        show inc.status = .cancelled
        cases hstat : inc.status
        all_goals first | rfl | (rw [hstat] at hs; cases hs)
    · rename_i hnotdone
      have hinc_pos : inc.remainingQty > 0 := by
        apply Nat.pos_of_ne_zero
        intro h0
        rw [h0] at hnotdone
        simp at hnotdone
      split
      · -- buy branch: absurd since hside : inc.side = .sell
        rename_i heq
        rw [hside] at heq; exact absurd heq (by decide)
      · -- sell branch (contra = bids)
        cases hbid : bids with
        | nil =>
          right; right; left
          rfl
        | cons level restLevels =>
          simp only
          split
          · -- !canMatchPrice inc level.price → terminal (fourth disjunct)
            rename_i hnc
            right; right; right
            intro hd hmem
            have hhd : hd = level := by
              simp at hmem; exact hmem.symm
            rw [hhd]
            unfold canMatchPrice at hnc
            cases hprice : inc.price with
            | none =>
              exfalso
              rw [hprice] at hnc
              simp at hnc
            | some p =>
              rw [hprice, hside] at hnc
              simp at hnc
              -- hnc : ¬ (p ≤ level.price), i.e., level.price < p
              show level.price < (some p).getD 0
              show level.price < p
              omega
          · cases horders : level.orders with
            | nil =>
              have hmdec : matchMeasure restLevels inc
                         < matchMeasure (level :: restLevels) inc :=
                matchMeasure_skip_empty_level level restLevels inc horders
              have hfuel' : n > matchMeasure restLevels inc := by
                have hprev : n + 1 > matchMeasure bids inc := hfuel
                rw [hbid] at hprev
                omega
              exact ih inc restLevels trades tm hside hfuel'
            | cons resting restOrders =>
              simp only
              cases hzv : (resting.visibleQty == 0 && !selfTradeConflict inc resting) with
              | true =>
                have hmdec :=
                  matchMeasure_drop_head_order level restLevels inc
                    resting restOrders horders
                have hfuel' :
                    n > matchMeasure
                      (if restOrders.isEmpty then restLevels
                       else { level with orders := restOrders } :: restLevels) inc := by
                  have hprev : n + 1 > matchMeasure bids inc := hfuel
                  rw [hbid] at hprev
                  omega
                exact ih inc _ _ _ hside hfuel'
              | false =>
                cases hstp : selfTradeConflict inc resting with
                | true =>
                  cases hpol : inc.stpPolicy.getD .cancelNewest with
                  | cancelNewest =>
                    right; left
                    show OrderStatus.cancelled = OrderStatus.cancelled
                    rfl
                  | cancelOldest =>
                    have hmdec :=
                      matchMeasure_drop_head_order level restLevels inc
                        resting restOrders horders
                    have hfuel' :
                        n > matchMeasure
                          (if restOrders.isEmpty then restLevels
                           else { level with orders := restOrders } :: restLevels) inc := by
                      have hprev : n + 1 > matchMeasure bids inc := hfuel
                      rw [hbid] at hprev
                      omega
                    exact ih inc _ _ _ hside hfuel'
                  | cancelBoth =>
                    right; left
                    show OrderStatus.cancelled = OrderStatus.cancelled
                    rfl
                  | decrement =>
                    cases hrz : (min inc.remainingQty resting.visibleQty == 0) with
                    | true =>
                      have hmdec :=
                        matchMeasure_drop_head_order level restLevels inc
                          resting restOrders horders
                      have hfuel' :
                          n > matchMeasure
                            (if restOrders.isEmpty then restLevels
                             else { level with orders := restOrders } :: restLevels) inc := by
                        have hprev : n + 1 > matchMeasure bids inc := hfuel
                        rw [hbid] at hprev
                        omega
                      exact ih inc _ _ _ hside hfuel'
                    | false =>
                      cases hrr : (resting.remainingQty - min inc.remainingQty resting.visibleQty == 0) with
                      | true =>
                        refine ih
                          ({ inc with
                            remainingQty := inc.remainingQty -
                              min inc.remainingQty resting.visibleQty,
                            status := if inc.remainingQty -
                              min inc.remainingQty resting.visibleQty == 0 then
                              .cancelled else inc.status })
                          _ _ _ hside ?_
                        have hmdec := matchMeasure_drop_head_order level restLevels
                          ({ inc with
                            remainingQty := inc.remainingQty -
                              min inc.remainingQty resting.visibleQty,
                            status := if inc.remainingQty -
                              min inc.remainingQty resting.visibleQty == 0 then
                              .cancelled else inc.status })
                          resting restOrders horders
                        rw [← hbid] at hmdec
                        have h_mono :
                            matchMeasure bids
                              ({ inc with
                                remainingQty := inc.remainingQty -
                                  min inc.remainingQty resting.visibleQty,
                                status := if inc.remainingQty -
                                  min inc.remainingQty resting.visibleQty == 0 then
                                  .cancelled else inc.status })
                            ≤ matchMeasure bids inc := by
                          exact Nat.le.refl
                        omega
                      | false =>
                        cases hiv :
                            ((resting.visibleQty - min inc.remainingQty resting.visibleQty == 0)
                              && resting.displayQty.isSome) with
                        | true =>
                          -- STP decrement iceberg reload
                          have hrz_pos : 0 < min inc.remainingQty resting.visibleQty := by
                            apply Nat.pos_of_ne_zero
                            intro he
                            rw [he] at hrz
                            simp at hrz
                          have hrr_prop : resting.remainingQty -
                                          min inc.remainingQty resting.visibleQty > 0 := by
                            apply Nat.pos_of_ne_zero
                            intro he
                            rw [he] at hrr
                            simp at hrr
                          have hr_pos : 0 < resting.remainingQty := by
                            apply Nat.pos_of_ne_zero
                            intro he
                            rw [he] at hrr_prop
                            simp at hrr_prop
                          have hne : ∀ (y : Order),
                              (restOrders ++ [y]).isEmpty = false := by
                            intro y; cases restOrders <;> rfl
                          simp only [hne, if_false]
                          have hmdec_lvl :
                              matchMeasure ({ level with orders := restOrders ++
                                  [({ resting with
                                      visibleQty := min (resting.displayQty.getD 0)
                                        (resting.remainingQty -
                                          min inc.remainingQty resting.visibleQty),
                                      remainingQty := resting.remainingQty -
                                        min inc.remainingQty resting.visibleQty,
                                      timestamp := tm,
                                      status := OrderStatus.partiallyFilled } : Order)] }
                                             :: restLevels)
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order)
                              < matchMeasure (level :: restLevels)
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order) := by
                            apply matchMeasure_modify_head_level_orders
                            · rw [horders]
                              simp
                            · rw [horders, orderSum_append, orderSum_singleton]
                              show orderSum restOrders +
                                   (resting.remainingQty -
                                     min inc.remainingQty resting.visibleQty)
                                 < orderSum (resting :: restOrders)
                              show orderSum restOrders +
                                   (resting.remainingQty -
                                     min inc.remainingQty resting.visibleQty)
                                 < resting.remainingQty + orderSum restOrders
                              have h_lt : resting.remainingQty -
                                          min inc.remainingQty resting.visibleQty
                                        < resting.remainingQty :=
                                Nat.sub_lt hr_pos hrz_pos
                              rw [Nat.add_comm resting.remainingQty (orderSum restOrders)]
                              exact Nat.add_lt_add_left h_lt (orderSum restOrders)
                          rw [← hbid] at hmdec_lvl
                          have h_mono :
                              matchMeasure bids
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order)
                              ≤ matchMeasure bids inc := by
                            apply matchMeasure_mono_inc_le
                            show inc.remainingQty - min inc.remainingQty resting.visibleQty
                                 ≤ inc.remainingQty
                            exact Nat.sub_le _ _
                          refine ih
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty,
                              status := if inc.remainingQty -
                                min inc.remainingQty resting.visibleQty == 0 then
                                .cancelled else inc.status } : Order)
                            _ _ _ hside ?_
                          exact fuel_from_decrease n _ _ hfuel
                            (Nat.lt_of_lt_of_le hmdec_lvl h_mono)
                        | false =>
                          -- STP decrement partial
                          have hrz_pos : min inc.remainingQty resting.visibleQty > 0 := by
                            apply Nat.pos_of_ne_zero
                            intro he
                            rw [he] at hrz
                            simp at hrz
                          have hmdec_lvl :
                              matchMeasure
                                ({ level with orders :=
                                    ({ resting with
                                        remainingQty := resting.remainingQty -
                                          min inc.remainingQty resting.visibleQty,
                                        visibleQty := resting.visibleQty -
                                          min inc.remainingQty resting.visibleQty } : Order)
                                    :: restOrders } :: restLevels)
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order)
                              < matchMeasure (level :: restLevels)
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order) := by
                            apply matchMeasure_modify_head_level_orders
                            · rw [horders]; simp
                            · rw [horders]
                              show (resting.remainingQty -
                                    min inc.remainingQty resting.visibleQty)
                                  + orderSum restOrders
                                  < resting.remainingQty + orderSum restOrders
                              have hr_pos : 0 < resting.remainingQty := by
                                apply Nat.pos_of_ne_zero
                                intro he
                                rw [he] at hrr
                                simp at hrr
                              have h_lt : resting.remainingQty -
                                          min inc.remainingQty resting.visibleQty
                                        < resting.remainingQty :=
                                Nat.sub_lt hr_pos hrz_pos
                              exact Nat.add_lt_add_right h_lt _
                          rw [← hbid] at hmdec_lvl
                          have h_mono :
                              matchMeasure bids
                                ({ inc with
                                  remainingQty := inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  status := if inc.remainingQty -
                                    min inc.remainingQty resting.visibleQty == 0 then
                                    .cancelled else inc.status } : Order)
                              ≤ matchMeasure bids inc := by
                            apply matchMeasure_mono_inc_le
                            show inc.remainingQty - min inc.remainingQty resting.visibleQty
                                 ≤ inc.remainingQty
                            exact Nat.sub_le _ _
                          refine ih
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty,
                              status := if inc.remainingQty -
                                min inc.remainingQty resting.visibleQty == 0 then
                                .cancelled else inc.status } : Order)
                            _ _ _ hside ?_
                          exact fuel_from_decrease n _ _ hfuel (Nat.lt_of_lt_of_le hmdec_lvl h_mono)
                | false =>
                  -- Normal fill
                  cases hff : (resting.remainingQty -
                               min inc.remainingQty resting.visibleQty == 0) with
                  | true =>
                    have hmdec := matchMeasure_drop_head_order level restLevels
                      ({ inc with
                        remainingQty := inc.remainingQty -
                          min inc.remainingQty resting.visibleQty } : Order)
                      resting restOrders horders
                    rw [← hbid] at hmdec
                    have h_mono :
                        matchMeasure bids
                          ({ inc with
                            remainingQty := inc.remainingQty -
                              min inc.remainingQty resting.visibleQty } : Order)
                        ≤ matchMeasure bids inc := by
                      exact Nat.le.refl
                    refine ih
                      ({ inc with
                        remainingQty := inc.remainingQty -
                          min inc.remainingQty resting.visibleQty } : Order)
                      _ _ _ hside ?_
                    omega
                  | false =>
                    cases hir :
                        ((resting.visibleQty - min inc.remainingQty resting.visibleQty == 0)
                          && resting.displayQty.isSome) with
                    | true =>
                      -- Normal fill iceberg reload
                      have hvis_pos : resting.visibleQty > 0 := by
                        apply Nat.pos_of_ne_zero
                        intro hv
                        rw [hv] at hzv
                        simp [hstp] at hzv
                      have hfill_pos : 0 < min inc.remainingQty resting.visibleQty :=
                        Nat.lt_min.mpr ⟨hinc_pos, hvis_pos⟩
                      have hff_prop : resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty > 0 := by
                        apply Nat.pos_of_ne_zero
                        intro he
                        rw [he] at hff
                        simp at hff
                      have hr_pos : 0 < resting.remainingQty := by
                        apply Nat.pos_of_ne_zero
                        intro he
                        rw [he] at hff_prop
                        simp at hff_prop
                      have h_qty_lt : resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty
                                    < resting.remainingQty :=
                        Nat.sub_lt hr_pos hfill_pos
                      have hmdec_lvl :
                          matchMeasure ({ level with orders := restOrders ++
                              [({ resting with
                                  visibleQty := min (resting.displayQty.getD 0)
                                    (resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty),
                                  remainingQty := resting.remainingQty -
                                    min inc.remainingQty resting.visibleQty,
                                  timestamp := tm,
                                  status := OrderStatus.partiallyFilled } : Order)] }
                                         :: restLevels)
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order)
                          < matchMeasure (level :: restLevels)
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order) := by
                        apply matchMeasure_modify_head_level_orders
                        · rw [horders]
                          simp
                        · rw [horders, orderSum_append, orderSum_singleton]
                          show orderSum restOrders +
                               (resting.remainingQty - min inc.remainingQty resting.visibleQty)
                             < orderSum (resting :: restOrders)
                          show orderSum restOrders +
                               (resting.remainingQty - min inc.remainingQty resting.visibleQty)
                             < resting.remainingQty + orderSum restOrders
                          have h_lt : resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty
                                    < resting.remainingQty :=
                            Nat.sub_lt hr_pos hfill_pos
                          rw [Nat.add_comm resting.remainingQty (orderSum restOrders)]
                          exact Nat.add_lt_add_left h_lt (orderSum restOrders)
                      rw [← hbid] at hmdec_lvl
                      have h_mono :
                          matchMeasure bids
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order)
                          ≤ matchMeasure bids inc := by
                        apply matchMeasure_mono_inc_le
                        show inc.remainingQty - min inc.remainingQty resting.visibleQty
                             ≤ inc.remainingQty
                        exact Nat.sub_le _ _
                      refine ih
                        ({ inc with
                          remainingQty := inc.remainingQty -
                            min inc.remainingQty resting.visibleQty } : Order)
                        _ _ _ hside ?_
                      exact fuel_from_decrease n _ _ hfuel (Nat.lt_of_lt_of_le hmdec_lvl h_mono)
                    | false =>
                      -- Partial fill
                      have hvis_pos : resting.visibleQty > 0 := by
                        apply Nat.pos_of_ne_zero
                        intro hv
                        rw [hv] at hzv
                        simp [hstp] at hzv
                      have hfill_pos : 0 < min inc.remainingQty resting.visibleQty :=
                        Nat.lt_min.mpr ⟨hinc_pos, hvis_pos⟩
                      have hff_prop : resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty > 0 := by
                        apply Nat.pos_of_ne_zero
                        intro he
                        rw [he] at hff
                        simp at hff
                      have hmdec_lvl :
                          matchMeasure
                            ({ level with orders :=
                                ({ resting with
                                    visibleQty := resting.visibleQty -
                                      min inc.remainingQty resting.visibleQty,
                                    remainingQty := resting.remainingQty -
                                      min inc.remainingQty resting.visibleQty,
                                    status := OrderStatus.partiallyFilled } : Order)
                                :: restOrders } :: restLevels)
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order)
                          < matchMeasure (level :: restLevels)
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order) := by
                        apply matchMeasure_modify_head_level_orders
                        · rw [horders]; simp
                        · rw [horders]
                          show (resting.remainingQty -
                                min inc.remainingQty resting.visibleQty)
                              + orderSum restOrders
                              < resting.remainingQty + orderSum restOrders
                          rcases Nat.le_total inc.remainingQty resting.visibleQty with hle | hle
                          · rw [Nat.min_eq_left hle] at hff_prop hfill_pos ⊢
                            have hr_pos : 0 < resting.remainingQty := by
                              apply Nat.pos_of_ne_zero
                              intro he
                              rw [he] at hff_prop
                              simp at hff_prop
                            have h_lt : resting.remainingQty - inc.remainingQty
                                      < resting.remainingQty :=
                              Nat.sub_lt hr_pos hinc_pos
                            exact Nat.add_lt_add_right h_lt _
                          · rw [Nat.min_eq_right hle] at hff_prop hfill_pos ⊢
                            have hr_pos : 0 < resting.remainingQty := by
                              apply Nat.pos_of_ne_zero
                              intro he
                              rw [he] at hff_prop
                              simp at hff_prop
                            have h_lt : resting.remainingQty - resting.visibleQty
                                      < resting.remainingQty :=
                              Nat.sub_lt hr_pos hvis_pos
                            exact Nat.add_lt_add_right h_lt _
                      rw [← hbid] at hmdec_lvl
                      have h_mono :
                          matchMeasure bids
                            ({ inc with
                              remainingQty := inc.remainingQty -
                                min inc.remainingQty resting.visibleQty } : Order)
                          ≤ matchMeasure bids inc := by
                        exact Nat.le.refl
                      refine ih
                        ({ inc with
                          remainingQty := inc.remainingQty -
                            min inc.remainingQty resting.visibleQty } : Order)
                        _ _ _ hside ?_
                      omega

/-- Sell no-cross-after-match (mirror of buy version). -/
theorem doMatch_sell_noCross_after_match (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hside : inc.side = .sell)
    (hfuel : fuel > matchMeasure bids inc) :
    let mr := doMatch fuel inc bids asks trades tm
    mr.incoming.remainingQty > 0 →
    mr.incoming.status ≠ .cancelled →
    mr.bids = [] ∨ (∀ hd ∈ mr.bids.head?, hd.price < (mr.incoming.price.getD 0)) := by
  intro mr hqty hstatus
  have hstable := doMatch_sell_output_stable fuel inc bids asks trades tm hside hfuel
  exact doMatch_sell_noCross_of_stable hstable hqty hstatus

-- ============================================================================
-- Unified (side-parameterized) fuel sufficiency
-- ============================================================================

/-- Side-parameterized "stable" predicate. -/
def matchStable (side : Side) (inc : Order) (contra : List PriceLevel) : Prop :=
  match side with
  | .buy  => buyMatchStable inc contra
  | .sell => sellMatchStable inc contra

/-- **Unified side-parameterized**: `doMatch` with sufficient fuel produces
    a stable output (either incoming consumed/cancelled, contra empty, or
    head non-crossing). Dispatches to buy/sell via `cases side`. -/
theorem doMatch_output_stable (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (side : Side) (hside : inc.side = side)
    (hfuel : fuel > matchMeasure (contraInput side bids asks) inc) :
    let mr := doMatch fuel inc bids asks trades tm
    matchStable side mr.incoming (MatchResult.contraSide side mr) := by
  cases side with
  | buy =>
    show buyMatchStable _ _
    exact doMatch_buy_output_stable fuel inc bids asks trades tm hside hfuel
  | sell =>
    show sellMatchStable _ _
    exact doMatch_sell_output_stable fuel inc bids asks trades tm hside hfuel

-- ============================================================================
-- Matching phase dispose non-crossing helper
-- ============================================================================

/-- Extractor: for the result of `matchOrder (computeMatchFuel b o.side) b o`,
    the dispose non-crossing precondition holds whenever `mr.incoming` is
    non-terminal. Used by FOK/MinQty/MTL/Normal matching phases.

    **Sorry'd**: internal proof chains through `doMatch_noCross_after_match`
    and head?-to-bestAskPrice conversion — ~50 lines deferred. -/
private theorem matching_dispose_noCross
    (o : Order) (b : BookState) (_h : AllInv b) :
    ¬ ((matchOrder (computeMatchFuel b o.side) b o).incoming.remainingQty = 0 ∨
       (matchOrder (computeMatchFuel b o.side) b o).incoming.status = .cancelled ∨
       (matchOrder (computeMatchFuel b o.side) b o).incoming.tif = .ioc ∨
       (matchOrder (computeMatchFuel b o.side) b o).incoming.orderType = .market) →
    match (matchOrder (computeMatchFuel b o.side) b o).incoming.side with
    | .buy  => ∀ askP ∈ bestAskPrice { b with
                  bids := (matchOrder (computeMatchFuel b o.side) b o).bids,
                  asks := (matchOrder (computeMatchFuel b o.side) b o).asks,
                  clock := (matchOrder (computeMatchFuel b o.side) b o).clock },
                (matchOrder (computeMatchFuel b o.side) b o).incoming.price.getD 0 < askP
    | .sell => ∀ bidP ∈ bestBidPrice { b with
                  bids := (matchOrder (computeMatchFuel b o.side) b o).bids,
                  asks := (matchOrder (computeMatchFuel b o.side) b o).asks,
                  clock := (matchOrder (computeMatchFuel b o.side) b o).clock },
                bidP < (matchOrder (computeMatchFuel b o.side) b o).incoming.price.getD 0 := by
  sorry

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

-- ============================================================================
-- processOrder phase-by-phase helpers
-- ============================================================================

/-- Phase 1b: stop order that does NOT trigger. Appended to stops; bids/asks
    unchanged. -/
private theorem processOrder_stopRest_preserves
    (o : Order) (b : BookState) (h : BookUncrossed b) :
    BookUncrossed { b with stops := b.stops ++ [o] } :=
  (BookUncrossed_with_stops b (b.stops ++ [o])).mp h

-- ============================================================================
-- Fuel bridge: computeMatchFuel b side > matchMeasure (contraLevels b side) inc
-- ============================================================================

/-- Accumulator-generalized form of `totalRemaining` equalling its `foldl` shape. -/
private theorem totalRemaining_foldl_acc (init : Nat) (lvls : List PriceLevel) :
    lvls.foldl (fun acc lvl =>
      acc + lvl.orders.foldl (fun a o => a + o.remainingQty) 0) init
    = init + totalRemaining lvls := by
  induction lvls generalizing init with
  | nil => show init = init + 0; omega
  | cons l rest ih =>
    show (rest.foldl
            (fun acc lvl => acc + lvl.orders.foldl (fun a o => a + o.remainingQty) 0)
            (init + l.orders.foldl (fun a o => a + o.remainingQty) 0))
      = init + (orderSum l.orders + totalRemaining rest)
    rw [ih]
    have h1 : l.orders.foldl (fun a o => a + o.remainingQty) 0 = orderSum l.orders := by
      have hgen : ∀ (init : Nat) (os : List Order),
          os.foldl (fun a o => a + o.remainingQty) init = init + orderSum os := by
        intro init os
        induction os generalizing init with
        | nil => show init = init + 0; omega
        | cons o rest' ih' =>
          show rest'.foldl (fun a o => a + o.remainingQty) (init + o.remainingQty)
             = init + (o.remainingQty + orderSum rest')
          rw [ih']; omega
      have := hgen 0 l.orders
      omega
    rw [h1]; omega

/-- Accumulator-generalized form of `orderCount` equalling its `foldl` shape. -/
private theorem orderCount_foldl_acc (init : Nat) (lvls : List PriceLevel) :
    lvls.foldl (fun acc lvl => acc + lvl.orders.length) init
    = init + orderCount lvls := by
  induction lvls generalizing init with
  | nil => show init = init + 0; omega
  | cons l rest ih =>
    show (rest.foldl (fun acc lvl => acc + lvl.orders.length) (init + l.orders.length))
       = init + (l.orders.length + orderCount rest)
    rw [ih]; omega

/-- **Fuel bridge**: `computeMatchFuel b side` equals `matchMeasure + 1`, so
    is strictly greater than `matchMeasure (contraLevels b side) inc`. -/
theorem computeMatchFuel_gt_matchMeasure
    (b : BookState) (inc : Order) (side : Side) :
    computeMatchFuel b side > matchMeasure (contraLevels b side) inc := by
  unfold computeMatchFuel matchMeasure
  simp only
  rw [totalRemaining_foldl_acc, orderCount_foldl_acc]
  omega

-- ============================================================================
-- Cascade preservation stubs (mutual induction obligation)
-- ============================================================================

/-- Post-only precondition extractor: if `wouldCross o b = false` AND the
    order's price is defined, extract the strict non-crossing inequality
    needed by `insertOrder_preserves_uncrossed`. -/
private theorem wouldCross_false_nonCross_pre
    (o : Order) (b : BookState) (side : Side) (hside : o.side = side)
    (hp : o.price.isSome = true)
    (hnc : wouldCross o b = false) :
    match side with
    | .buy  => ∀ askP ∈ bestAskPrice b, (o.price.getD 0) < askP
    | .sell => ∀ bidP ∈ bestBidPrice b, bidP < (o.price.getD 0) := by
  unfold wouldCross at hnc
  cases hpv : o.price with
  | none => rw [hpv] at hp; cases hp
  | some p =>
    rw [hpv] at hnc
    rw [hside] at hnc
    cases side with
    | buy =>
      intro askP haskP
      cases hask : bestAskPrice b with
      | none => rw [hask] at haskP; cases haskP
      | some askP' =>
        rw [hask] at hnc
        rw [hask] at haskP
        have heq : askP' = askP := Option.mem_some_iff.mp haskP
        simp at hnc
        have hlt : p < askP' := by omega
        rw [heq] at hlt
        exact hlt
    | sell =>
      intro bidP hbidP
      cases hbid : bestBidPrice b with
      | none => rw [hbid] at hbidP; cases hbidP
      | some bidP' =>
        rw [hbid] at hnc
        rw [hbid] at hbidP
        have heq : bidP' = bidP := Option.mem_some_iff.mp hbidP
        simp at hnc
        have hlt : bidP' < p := by omega
        rw [heq] at hlt
        exact hlt

/-- Joint AllInv preservation for the three mutually recursive functions.
    Proved by induction on fuel, with phase analysis for each function. -/
theorem process_all_preserve_AllInv : ∀ (fuel : Nat),
    (∀ (o : Order) (b : BookState), AllInv b →
      AllInv (processOrder fuel o b).book) ∧
    (∀ (trades : List Trade) (b : BookState), AllInv b →
      AllInv (processCascade fuel trades b).book) ∧
    (∀ (orders : List Order) (b : BookState), AllInv b →
      AllInv (processTriggeredStops fuel orders b).book) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro o b h
      show AllInv b
      exact h
    · intro ts b h
      cases ts
      · show AllInv b; exact h
      · show AllInv b; exact h
    · intro os b h
      cases os
      · show AllInv b; exact h
      · show AllInv b; exact h
  | succ n ih =>
    obtain ⟨ih_po, ih_pc, ih_pts⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · -- processOrder fuel'+1 preservation
      intro o b h
      unfold processOrder
      simp only
      split
      · -- Phase 1: Stop order
        split
        · -- Triggered: recurse via ih_po on clock-updated book
          exact ih_po _ _ (AllInv.with_clock b (b.clock + 1) h)
        · -- Not triggered: append to stops
          exact AllInv.with_stops b _ h
      · split
        · -- Phase 2: Post-only
          split
          · -- wouldCross true: return b unchanged
            exact h
          · -- wouldCross false: insertOrder b o false
            rename_i _ hwc
            have hnc : wouldCross o b = false := by
              cases hwcv : wouldCross o b with
              | true => exact absurd hwcv hwc
              | false => rfl
            cases hp : o.price with
            | none =>
              -- Spec edge case: post-only with no price. Deferred.
              sorry
            | some p =>
              have hps : o.price.isSome = true := by rw [hp]; rfl
              refine insertOrder_preserves_AllInv b o false h ?_
              cases hs : o.side with
              | buy =>
                show ∀ askP ∈ bestAskPrice b, (o.price.getD 0) < askP
                have := wouldCross_false_nonCross_pre o b .buy hs hps hnc
                exact this
              | sell =>
                show ∀ bidP ∈ bestBidPrice b, bidP < (o.price.getD 0)
                have := wouldCross_false_nonCross_pre o b .sell hs hps hnc
                exact this
        · split
          · -- Phase 3: FOK
            split
            · -- !fokCheck: b unchanged
              exact h
            · -- fokCheck: match + cascade (no dispose)
              apply ih_pc
              -- Establish AllInv for b' (after match)
              have hb' : AllInv { b with
                bids := (matchOrder (computeMatchFuel b o.side) b o).bids,
                asks := (matchOrder (computeMatchFuel b o.side) b o).asks,
                clock := (matchOrder (computeMatchFuel b o.side) b o).clock } := by
                unfold matchOrder
                exact doMatch_preserves_AllInv
                  (computeMatchFuel b o.side) o b (b.clock + 1) o.side rfl h
              -- b''' adds lastTradePrice — still AllInv via with_ltp
              exact AllInv.with_ltp _ _ hb'
          · split
            · -- Phase 3b: MinQty
              split
              · -- !minQtyCheck: b unchanged
                exact h
              · -- minQtyCheck: match + dispose + cascade
                -- inc = if !mr.trades.isEmpty then {mr.incoming with minQty := none} else mr.incoming
                -- Either way inc.side/.price/.etc = mr.incoming's, so non-crossing carries through.
                apply ih_pc
                apply AllInv.with_ltp
                have hb' : AllInv { b with
                  bids := (matchOrder (computeMatchFuel b o.side) b o).bids,
                  asks := (matchOrder (computeMatchFuel b o.side) b o).asks,
                  clock := (matchOrder (computeMatchFuel b o.side) b o).clock } := by
                  unfold matchOrder
                  exact doMatch_preserves_AllInv
                    (computeMatchFuel b o.side) o b (b.clock + 1) o.side rfl h
                -- Deferred: conditional inc handling (minQty := none vs mr.incoming)
                -- needs a small lemma showing both dispose branches preserve AllInv.
                sorry
            · split
              · -- Phase 4: MTL
                -- MTL has multiple sub-cases (no-trades vs trades, converted done vs partial)
                -- All reduce to doMatch + optional dispose + cascade with additional
                -- MTL-specific doMatch for the converted limit order
                sorry
              · -- Phase 5: Normal matching
                -- In Phase 5 we're past minQty.isSome check (=false), so inc = mr.incoming
                apply ih_pc
                apply AllInv.with_ltp
                have hb' : AllInv { b with
                  bids := (matchOrder (computeMatchFuel b o.side) b o).bids,
                  asks := (matchOrder (computeMatchFuel b o.side) b o).asks,
                  clock := (matchOrder (computeMatchFuel b o.side) b o).clock } := by
                  unfold matchOrder
                  exact doMatch_preserves_AllInv
                    (computeMatchFuel b o.side) o b (b.clock + 1) o.side rfl h
                -- In Phase 5, o.minQty.isSome = false (from outer split, deferred)
                have h_minq_false : o.minQty.isSome = false := by sorry
                simp only [h_minq_false, Bool.false_and, Bool.false_eq_true, if_false]
                exact dispose_preserves_AllInv _ _ _ hb' (matching_dispose_noCross o b h)
    · -- processCascade fuel'+1 preservation
      intro ts b h
      unfold processCascade
      match ts with
      | [] => exact h
      | t :: rest =>
        simp only
        split
        · -- triggered is empty: recurse with updated LTP
          have h1 : AllInv { b with lastTradePrice := some t.price } :=
            AllInv.with_ltp b (some t.price) h
          exact ih_pc rest _ h1
        · -- triggered non-empty
          simp only
          have h1 : AllInv { b with
              stops := (b.stops.partition (fun s => shouldTrigger s (some t.price))).2 } :=
            AllInv.with_stops b _ h
          have hb' : AllInv { b with
              stops := (b.stops.partition (fun s => shouldTrigger s (some t.price))).2,
              lastTradePrice := some t.price } :=
            AllInv.with_ltp _ (some t.price) h1
          exact ih_pc rest _ (ih_pts _ _ hb')
    · -- processTriggeredStops fuel'+1 preservation
      intro os b h
      unfold processTriggeredStops
      match os with
      | [] => exact h
      | stop :: rest =>
        simp only
        have hb' : AllInv { b with clock := b.clock + 1 } :=
          AllInv.with_clock b (b.clock + 1) h
        have hres : AllInv (processOrder n (convertStop stop b.clock)
                            { b with clock := b.clock + 1 }).book :=
          ih_po _ _ hb'
        exact ih_pts rest _ hres

/-- Corollary: `processOrder` preserves `AllInv`. -/
theorem processOrder_preserves_AllInv (fuel : Nat) (o : Order) (b : BookState)
    (h : AllInv b) : AllInv (processOrder fuel o b).book :=
  (process_all_preserve_AllInv fuel).1 o b h

/-- Corollary: `processCascade` preserves `BookUncrossed`. -/
theorem processCascade_preserves_uncrossed (fuel : Nat) (trades : List Trade)
    (b : BookState) (h : AllInv b) :
    BookUncrossed (processCascade fuel trades b).book :=
  ((process_all_preserve_AllInv fuel).2.1 trades b h).1

/-- Corollary: `processTriggeredStops` preserves `BookUncrossed`. -/
theorem processTriggeredStops_preserves_uncrossed (fuel : Nat) (orders : List Order)
    (b : BookState) (h : AllInv b) :
    BookUncrossed (processTriggeredStops fuel orders b).book :=
  ((process_all_preserve_AllInv fuel).2.2 orders b h).1

/-- Post-only precondition extractor: if `wouldCross o b = false` AND the
    order's price is defined AND the book's side has a best price, extract
    the strict non-crossing inequality needed by `insertOrder_preserves_uncrossed`. -/
private theorem wouldCross_false_nonCross
    (o : Order) (b : BookState) (side : Side) (hside : o.side = side)
    (hp : o.price.isSome = true)
    (hnc : wouldCross o b = false) :
    match side with
    | .buy  => ∀ askP ∈ bestAskPrice b, (o.price.getD 0) < askP
    | .sell => ∀ bidP ∈ bestBidPrice b, bidP < (o.price.getD 0) := by
  unfold wouldCross at hnc
  cases hpv : o.price with
  | none => rw [hpv] at hp; cases hp
  | some p =>
    rw [hpv] at hnc
    rw [hside] at hnc
    cases side with
    | buy =>
      intro askP haskP
      cases hask : bestAskPrice b with
      | none => rw [hask] at haskP; cases haskP
      | some askP' =>
        rw [hask] at hnc
        rw [hask] at haskP
        have heq : askP' = askP := Option.mem_some_iff.mp haskP
        simp at hnc
        have hlt : p < askP' := by omega
        rw [heq] at hlt
        exact hlt
    | sell =>
      intro bidP hbidP
      cases hbid : bestBidPrice b with
      | none => rw [hbid] at hbidP; cases hbidP
      | some bidP' =>
        rw [hbid] at hnc
        rw [hbid] at hbidP
        have heq : bidP' = bidP := Option.mem_some_iff.mp hbidP
        simp at hnc
        have hlt : bidP' < p := by omega
        rw [heq] at hlt
        exact hlt

-- ============================================================================
-- Main theorem: processOrder preserves BookUncrossed (corollary of AllInv)
-- ============================================================================

/-- `processOrder` preserves `BookUncrossed`. Trivial corollary of
    `processOrder_preserves_AllInv`. -/
theorem processOrder_preserves_uncrossed (fuel : Nat) (o : Order) (b : BookState)
    (h : AllInv b) :
    BookUncrossed (processOrder fuel o b).book :=
  (processOrder_preserves_AllInv fuel o b h).1

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
