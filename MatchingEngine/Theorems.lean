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

-- ============================================================================
-- doMatch buy-side no-cross after matching
-- ============================================================================

/-- Buy-side "stable" predicate: doMatch has nothing more to do. Either the
    incoming is consumed/cancelled, or the contra side is empty, or the head
    of the contra side is non-crossing (price strictly above `inc.price`). -/
def buyMatchStable (inc : Order) (asks : List PriceLevel) : Prop :=
  inc.remainingQty = 0 ∨ inc.status = .cancelled ∨ asks = [] ∨
  (∀ hd ∈ asks.head?, (inc.price.getD 0) < hd.price)

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

/-- Well-founded measure for `doMatch` progress. Includes
    `totalRemaining + orderCount + contra.length + inc.remainingQty` so
    that EVERY non-terminal recursive step strictly decreases it. Matches
    the structure of `computeMatchFuel`. -/
def matchMeasure (contra : List PriceLevel) (inc : Order) : Nat :=
  totalRemaining contra + orderCount contra + contra.length + inc.remainingQty

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
    · -- Not terminal: split on inc.side
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
            sorry
          · match horders : level.orders with
            | [] =>
              -- Empty level skip — apply IH with matchMeasure_skip_empty_level
              -- Recursive call: doMatch n inc bids restLevels trades tm
              have hmdec : matchMeasure restLevels inc
                         < matchMeasure (level :: restLevels) inc :=
                matchMeasure_skip_empty_level level restLevels inc horders
              -- fuel sufficient for the recursive call: n > matchMeasure restLevels inc
              have hfuel' : n > matchMeasure restLevels inc := by
                have hprev : n + 1 > matchMeasure asks inc := hfuel
                rw [hask] at hprev
                omega
              exact ih inc restLevels trades tm hside hfuel'
            | resting :: restOrders =>
              sorry
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
-- Main theorem (scaffold with per-phase sorries)
-- ============================================================================

/-- SORRY: processOrder preserves `BookUncrossed`. Scaffold with closed easy
    phases and sorries for phases that require fuel sufficiency or mutual
    induction with the cascade. -/
theorem processOrder_preserves_uncrossed (fuel : Nat) (o : Order) (b : BookState)
    (h : AllInv b) :
    BookUncrossed (processOrder fuel o b).book := by
  induction fuel generalizing o b with
  | zero =>
    -- fuel=0: returns b unchanged
    show BookUncrossed b
    exact h.1
  | succ n ih =>
    unfold processOrder
    simp only
    split
    · -- Phase 1: Stop order
      split
      · -- Triggered: recurse with converted stop + updated clock.
        -- Needs AllInv on clock-updated book (straightforward via AllInv.with_clock),
        -- and IH. But IH has AllInv as precondition — currently AllInv includes
        -- sortedness, which is preserved by clock update. Apply IH.
        apply ih
        exact AllInv.with_clock b (b.clock + 1) h
      · -- Not triggered: append to stops
        show BookUncrossed { b with stops := b.stops ++ [o] }
        exact processOrder_stopRest_preserves o b h.1
    · split
      · -- Phase 2: Post-only
        split
        · -- wouldCross true: return b unchanged
          show BookUncrossed b
          exact h.1
        · -- wouldCross false: insertOrder b o false
          show BookUncrossed (insertOrder b o false)
          rename_i _ hwc
          have hnc : wouldCross o b = false := by
            cases hwcv : wouldCross o b with
            | true => exact absurd hwcv hwc
            | false => rfl
          -- Need to know o.price.isSome for the post-only phase.
          -- Post-only orders without price are a spec edge case; sorry for now.
          sorry
      · split
        · -- Phase 3: FOK
          split
          · -- !fokCheck: return b unchanged
            show BookUncrossed b
            exact h.1
          · -- fokCheck: match + dispose + cascade
            -- Needs fuel sufficiency (no-cross after match) + cascade IH.
            sorry
        · split
          · -- Phase 3b: MinQty
            split
            · -- !minQtyCheck: return b unchanged
              show BookUncrossed b
              exact h.1
            · -- minQtyCheck: match + dispose + cascade
              sorry
          · split
            · -- Phase 4: MTL
              sorry
            · -- Phase 5: Normal matching
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
