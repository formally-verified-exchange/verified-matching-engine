import MatchingEngine.Theorems

set_option maxHeartbeats 4000000

/-!
# Matching Engine — Full Invariant Preservation

`Theorems.lean` proves preservation of `AllInv` (uncrossed + sorted levels).
This file proves preservation of the remaining §13 invariants:

* INV-1  `NoEmptyLevels`
* INV-5  `NoGhosts`
* INV-6  `StatusConsistency`
* INV-7  `FIFOWithinLevel`
* INV-8  `NoRestingMarkets`
* INV-13 `NoRestingMTL`
* INV-14 `NoRestingMinQty`

and the two trade-event guarantees

* INV-11 `PostOnlyGuarantee`
* INV-12 `STPGuarantee`

culminating in `process_preserves_FullBookInv` and
`process_emits_safe_trades`.

## Why a timestamp bound is part of the bundle

`FIFOWithinLevel` (timestamps strictly increasing within a level) is *not*
preserved on its own: both queue-appending operations (iceberg reload in
`doMatch`, resting insertion in `insertOrder`) put an order at the back of a
level and therefore need to know that the appended order is strictly newer
than everything already queued there. The load-bearing fact is a clock
bound — every order resting on the book carries a timestamp below the
book's clock — so the bundle `RestOk` is indexed by that bound and threaded
through every lemma.
-/

-- ============================================================================
-- The structural bundle
-- ============================================================================

/-- Per-order conditions for an order that is allowed to rest on the book:
    INV-5 (no ghosts), INV-6 (status), INV-8 (no markets), INV-13 (no MTL),
    INV-14 (no minQty), plus the timestamp bound that supports INV-7. -/
def RestOk (n : Timestamp) (o : Order) : Prop :=
  0 < o.remainingQty ∧
  (o.status = OrderStatus.new_ ∨ o.status = OrderStatus.partiallyFilled) ∧
  o.orderType ≠ OrderType.market ∧
  o.orderType ≠ OrderType.marketToLimit ∧
  o.minQty = none ∧
  o.timestamp < n

/-- A single price level is well formed: nonempty (INV-1), FIFO-ordered
    (INV-7), and every order in it may rest (`RestOk`). -/
def LevelOk (n : Timestamp) (l : PriceLevel) : Prop :=
  l.orders ≠ [] ∧ FIFOLevel l.orders ∧ ∀ o ∈ l.orders, RestOk n o

/-- One side of the book is well formed. -/
def SideOk (n : Timestamp) (lvls : List PriceLevel) : Prop :=
  ∀ l ∈ lvls, LevelOk n l

/-- The structural bundle at an explicit timestamp bound. -/
def BookOkAt (n : Timestamp) (b : BookState) : Prop :=
  SideOk n b.bids ∧ SideOk n b.asks

/-- The structural bundle at the book's own clock: every resting order is
    strictly older than the clock. -/
def BookOk (b : BookState) : Prop := BookOkAt b.clock b

-- ============================================================================
-- Monotonicity in the timestamp bound
-- ============================================================================

theorem RestOk_mono {n m : Timestamp} {o : Order} (hnm : n ≤ m) (h : RestOk n o) :
    RestOk m o :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, Nat.lt_of_lt_of_le h.2.2.2.2.2 hnm⟩

theorem LevelOk_mono {n m : Timestamp} {l : PriceLevel} (hnm : n ≤ m) (h : LevelOk n l) :
    LevelOk m l :=
  ⟨h.1, h.2.1, fun o ho => RestOk_mono hnm (h.2.2 o ho)⟩

theorem SideOk_mono {n m : Timestamp} {lvls : List PriceLevel} (hnm : n ≤ m)
    (h : SideOk n lvls) : SideOk m lvls :=
  fun l hl => LevelOk_mono hnm (h l hl)

theorem BookOkAt_mono {n m : Timestamp} {b : BookState} (hnm : n ≤ m)
    (h : BookOkAt n b) : BookOkAt m b :=
  ⟨SideOk_mono hnm h.1, SideOk_mono hnm h.2⟩

-- ============================================================================
-- FIFO list lemmas
-- ============================================================================

theorem FIFOLevel_nil : FIFOLevel [] := List.Pairwise.nil

theorem FIFOLevel_tail {o : Order} {rest : List Order} (h : FIFOLevel (o :: rest)) :
    FIFOLevel rest := (List.pairwise_cons.mp h).2

theorem FIFOLevel_head_lt {o : Order} {rest : List Order} (h : FIFOLevel (o :: rest)) :
    ∀ x ∈ rest, o.timestamp < x.timestamp := (List.pairwise_cons.mp h).1

/-- Replacing the head of a FIFO queue by an order with the same timestamp
    keeps the queue FIFO. -/
theorem FIFOLevel_replace_head {o o' : Order} {rest : List Order}
    (h : FIFOLevel (o :: rest)) (hts : o'.timestamp = o.timestamp) :
    FIFOLevel (o' :: rest) := by
  unfold FIFOLevel at h ⊢
  rw [List.pairwise_cons] at h ⊢
  exact ⟨fun x hx => hts ▸ h.1 x hx, h.2⟩

/-- Appending a strictly newer order to the back of a FIFO queue keeps it
    FIFO. This is the iceberg-reload / resting-insertion case. -/
theorem FIFOLevel_append_newest {orders : List Order} {o : Order}
    (h : FIFOLevel orders) (hnew : ∀ x ∈ orders, x.timestamp < o.timestamp) :
    FIFOLevel (orders ++ [o]) := by
  rw [FIFOLevel, List.pairwise_append]
  refine ⟨h, List.pairwise_singleton _ _, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton] at hb
  exact hb ▸ hnew a ha

-- ============================================================================
-- Level-shape lemmas used by the `doMatch` branches
-- ============================================================================

theorem SideOk_tail {n : Timestamp} {l : PriceLevel} {rest : List PriceLevel}
    (h : SideOk n (l :: rest)) : SideOk n rest :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem SideOk_head {n : Timestamp} {l : PriceLevel} {rest : List PriceLevel}
    (h : SideOk n (l :: rest)) : LevelOk n l := h l List.mem_cons_self

theorem SideOk_cons {n : Timestamp} {l : PriceLevel} {rest : List PriceLevel}
    (hl : LevelOk n l) (hrest : SideOk n rest) : SideOk n (l :: rest) := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · exact h ▸ hl
  · exact hrest x h

/-- Dropping the head order of the head level (and the level itself if it
    becomes empty) preserves side well-formedness. This is the shape used by
    every "remove the resting order" branch of `doMatch`. -/
theorem SideOk_drop_head_order {n : Timestamp} {level : PriceLevel}
    {resting : Order} {restOrders : List Order} {restLevels : List PriceLevel}
    (h : SideOk n (level :: restLevels)) (hord : level.orders = resting :: restOrders) :
    SideOk n (if restOrders.isEmpty then restLevels
              else { level with orders := restOrders } :: restLevels) := by
  have hlev := SideOk_head h
  have htail := SideOk_tail h
  simp only [LevelOk, hord] at hlev
  by_cases he : restOrders.isEmpty
  · rw [if_pos he]; exact htail
  · rw [if_neg he]
    refine SideOk_cons ⟨?_, ?_, ?_⟩ htail
    · simpa using he
    · exact FIFOLevel_tail hlev.2.1
    · intro o ho; exact hlev.2.2 o (List.mem_cons_of_mem _ ho)

/-- Replacing the head order of the head level by an order that is still
    `RestOk` and carries the same timestamp preserves well-formedness.
    This is the partial-fill / STP-decrement shape. -/
theorem SideOk_replace_head_order {n : Timestamp} {level : PriceLevel}
    {resting o' : Order} {restOrders : List Order} {restLevels : List PriceLevel}
    (h : SideOk n (level :: restLevels)) (hord : level.orders = resting :: restOrders)
    (hok : RestOk n o') (hts : o'.timestamp = resting.timestamp) :
    SideOk n ({ level with orders := o' :: restOrders } :: restLevels) := by
  have hlev := SideOk_head h
  have htail := SideOk_tail h
  simp only [LevelOk, hord] at hlev
  refine SideOk_cons ⟨by simp, ?_, ?_⟩ htail
  · exact FIFOLevel_replace_head hlev.2.1 hts
  · intro o ho
    rcases List.mem_cons.mp ho with hh | hh
    · exact hh ▸ hok
    · exact hlev.2.2 o (List.mem_cons_of_mem _ hh)

/-- Moving a reloaded iceberg slice to the back of its level with a fresh
    timestamp `n` preserves well-formedness at the raised bound `n + 1`.
    This is the iceberg-reload shape. -/
theorem SideOk_reload_back {n : Timestamp} {level : PriceLevel}
    {resting reloaded : Order} {restOrders : List Order} {restLevels : List PriceLevel}
    (h : SideOk n (level :: restLevels)) (hord : level.orders = resting :: restOrders)
    (hok : RestOk (n + 1) reloaded) (hts : reloaded.timestamp = n) :
    SideOk (n + 1) ({ level with orders := restOrders ++ [reloaded] } :: restLevels) := by
  have hlev := SideOk_head h
  have htail := SideOk_tail h
  simp only [LevelOk, hord] at hlev
  refine SideOk_cons ⟨?_, ?_, ?_⟩ (SideOk_mono (Nat.le_succ n) htail)
  · simp
  · refine FIFOLevel_append_newest (FIFOLevel_tail hlev.2.1) ?_
    intro x hx
    rw [hts]
    exact (hlev.2.2 x (List.mem_cons_of_mem _ hx)).2.2.2.2.2
  · intro o ho
    rcases List.mem_append.mp ho with hh | hh
    · exact RestOk_mono (Nat.le_succ n) (hlev.2.2 o (List.mem_cons_of_mem _ hh))
    · rw [List.mem_singleton] at hh; exact hh ▸ hok

/-- Variant of `SideOk_reload_back` matching the `if newQueue.isEmpty` shape
    used by the STP-DECREMENT reload branch (the guard is never taken, since
    a queue ending in the reloaded slice is nonempty). -/
theorem SideOk_reload_back_if {n : Timestamp} {level : PriceLevel}
    {resting reloaded : Order} {restOrders : List Order} {restLevels : List PriceLevel}
    (h : SideOk n (level :: restLevels)) (hord : level.orders = resting :: restOrders)
    (hok : RestOk (n + 1) reloaded) (hts : reloaded.timestamp = n) :
    SideOk (n + 1) (if (restOrders ++ [reloaded]).isEmpty then restLevels
                    else { level with orders := restOrders ++ [reloaded] } :: restLevels) := by
  rw [if_neg (by simp)]
  exact SideOk_reload_back h hord hok hts

/-- The head order of the head level is `RestOk`. -/
theorem RestOk_of_head {n : Timestamp} {level : PriceLevel} {resting : Order}
    {restOrders : List Order} {restLevels : List PriceLevel}
    (h : SideOk n (level :: restLevels)) (hord : level.orders = resting :: restOrders) :
    RestOk n resting := by
  have hlev := SideOk_head h
  simp only [LevelOk, hord] at hlev
  exact hlev.2.2 resting List.mem_cons_self

-- ============================================================================
-- `doMatch` preserves the structural bundle
-- ============================================================================

/-- Both sides of a `MatchResult` are well formed at its own clock. -/
def MROk (r : MatchResult) : Prop :=
  SideOk r.clock r.bids ∧ SideOk r.clock r.asks

theorem doMatch_preserves_SideOk (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hb : SideOk tm bids) (ha : SideOk tm asks) :
    MROk (doMatch fuel inc bids asks trades tm) := by
  induction fuel generalizing inc bids asks trades tm with
  | zero => exact ⟨hb, ha⟩
  | succ n ih =>
    cases hside : inc.side with
    | buy =>
      cases asks with
      | nil =>
        unfold doMatch; simp only [hside]
        split
        · exact ⟨hb, ha⟩
        · exact ⟨hb, ha⟩
      | cons level restLevels =>
        obtain ⟨lprice, lorders⟩ := level
        cases lorders with
        | nil =>
          unfold doMatch; simp only [hside]
          split
          · exact ⟨hb, ha⟩
          · split
            · exact ⟨hb, ha⟩
            · -- defensive empty-level skip (unreachable under INV-1)
              exact ih inc bids restLevels trades tm hb (SideOk_tail ha)
        | cons resting restOrders =>
          have hr := RestOk_of_head ha rfl
          unfold doMatch; simp only [hside]
          split
          · exact ⟨hb, ha⟩
          · split
            · exact ⟨hb, ha⟩
            · split
              · -- zero-visible non-conflicting order: drop it
                exact ih inc bids _ trades tm hb (SideOk_drop_head_order ha rfl)
              · split
                · -- §8.3 STP handling
                  split
                  · -- CANCEL_NEWEST: incoming cancelled, book untouched
                    exact ⟨hb, ha⟩
                  · -- CANCEL_OLDEST: resting removed
                    exact ih inc bids _ trades tm hb (SideOk_drop_head_order ha rfl)
                  · -- CANCEL_BOTH: terminal, resting removed
                    exact ⟨hb, SideOk_drop_head_order ha rfl⟩
                  · -- DECREMENT
                    split
                    · -- nothing to decrement: remove the stranded order
                      exact ih inc bids _ trades tm hb (SideOk_drop_head_order ha rfl)
                    · split
                      · -- resting fully decremented: remove it
                        exact ih _ bids _ trades tm hb (SideOk_drop_head_order ha rfl)
                      · split
                        · -- BUG-2 fix: reload iceberg at the back, fresh timestamp
                          rename_i hrem _
                          refine ih _ bids _ trades (tm + 1)
                            (SideOk_mono (Nat.le_succ _) hb) ?_
                          refine SideOk_reload_back_if ha rfl ?_ rfl
                          exact ⟨by simp at hrem; exact Nat.pos_of_ne_zero hrem, Or.inr rfl,
                                 hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, Nat.lt_succ_self _⟩
                        · -- partial decrement: resting keeps its queue position
                          rename_i hrem _
                          refine ih _ bids _ trades tm hb ?_
                          refine SideOk_replace_head_order ha rfl ?_ rfl
                          exact ⟨by simp at hrem; exact Nat.pos_of_ne_zero hrem, hr.2.1,
                                 hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩
                · -- normal fill
                  split
                  · -- resting fully filled: remove it
                    exact ih _ bids _ _ tm hb (SideOk_drop_head_order ha rfl)
                  · split
                    · -- §7.5 iceberg reload: move to the back, fresh timestamp
                      rename_i hrem _
                      refine ih _ bids _ _ (tm + 1) (SideOk_mono (Nat.le_succ _) hb) ?_
                      refine SideOk_reload_back ha rfl ?_ rfl
                      exact ⟨by simp at hrem; exact Nat.pos_of_ne_zero hrem, Or.inr rfl,
                             hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, Nat.lt_succ_self _⟩
                    · -- partial fill: resting keeps its queue position
                      rename_i hrem _
                      refine ih _ bids _ _ tm hb ?_
                      refine SideOk_replace_head_order ha rfl ?_ rfl
                      exact ⟨by simp at hrem; exact Nat.pos_of_ne_zero hrem, Or.inr rfl,
                             hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩
    | sell =>
      cases bids with
      | nil =>
        unfold doMatch; simp only [hside]
        split
        · exact ⟨hb, ha⟩
        · exact ⟨hb, ha⟩
      | cons level restLevels =>
        obtain ⟨lprice, lorders⟩ := level
        cases lorders with
        | nil =>
          unfold doMatch; simp only [hside]
          split
          · exact ⟨hb, ha⟩
          · split
            · exact ⟨hb, ha⟩
            · -- defensive empty-level skip (unreachable under INV-1)
              exact ih inc restLevels asks trades tm (SideOk_tail hb) ha
        | cons resting restOrders =>
          have hr := RestOk_of_head hb rfl
          unfold doMatch; simp only [hside]
          split
          · exact ⟨hb, ha⟩
          · split
            · exact ⟨hb, ha⟩
            · split
              · -- zero-visible non-conflicting order: drop it
                exact ih inc _ asks trades tm (SideOk_drop_head_order hb rfl) ha
              · split
                · -- §8.3 STP handling
                  split
                  · -- CANCEL_NEWEST: incoming cancelled, book untouched
                    exact ⟨hb, ha⟩
                  · -- CANCEL_OLDEST: resting removed
                    exact ih inc _ asks trades tm (SideOk_drop_head_order hb rfl) ha
                  · -- CANCEL_BOTH: terminal, resting removed
                    exact ⟨SideOk_drop_head_order hb rfl, ha⟩
                  · -- DECREMENT
                    split
                    · -- nothing to decrement: remove the stranded order
                      exact ih inc _ asks trades tm (SideOk_drop_head_order hb rfl) ha
                    · split
                      · -- resting fully decremented: remove it
                        exact ih _ _ asks trades tm (SideOk_drop_head_order hb rfl) ha
                      · split
                        · -- BUG-2 fix: reload iceberg at the back, fresh timestamp
                          rename_i hrem _
                          refine ih _ _ asks trades (tm + 1) ?_
                            (SideOk_mono (Nat.le_succ _) ha)
                          refine SideOk_reload_back_if hb rfl ?_ rfl
                          exact ⟨by simp at hrem; exact Nat.pos_of_ne_zero hrem, Or.inr rfl,
                                 hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, Nat.lt_succ_self _⟩
                        · -- partial decrement: resting keeps its queue position
                          rename_i hrem _
                          refine ih _ _ asks trades tm ?_ ha
                          refine SideOk_replace_head_order hb rfl ?_ rfl
                          exact ⟨by simp at hrem; exact Nat.pos_of_ne_zero hrem, hr.2.1,
                                 hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩
                · -- normal fill
                  split
                  · -- resting fully filled: remove it
                    exact ih _ _ asks _ tm (SideOk_drop_head_order hb rfl) ha
                  · split
                    · -- §7.5 iceberg reload: move to the back, fresh timestamp
                      rename_i hrem _
                      refine ih _ _ asks _ (tm + 1) ?_ (SideOk_mono (Nat.le_succ _) ha)
                      refine SideOk_reload_back hb rfl ?_ rfl
                      exact ⟨by simp at hrem; exact Nat.pos_of_ne_zero hrem, Or.inr rfl,
                             hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, Nat.lt_succ_self _⟩
                    · -- partial fill: resting keeps its queue position
                      rename_i hrem _
                      refine ih _ _ asks _ tm ?_ ha
                      refine SideOk_replace_head_order hb rfl ?_ rfl
                      exact ⟨by simp at hrem; exact Nat.pos_of_ne_zero hrem, Or.inr rfl,
                             hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩


-- ============================================================================
-- `doMatch` plumbing: clock monotonicity, own-side stability, incoming fields
-- ============================================================================

/-- The match clock never runs backwards. Only the iceberg-reload branches
    advance it (by one, to stamp the reloaded slice). -/
theorem doMatch_clock_ge (fuel : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp) :
    tm ≤ (doMatch fuel inc bids asks trades tm).clock := by
  induction fuel generalizing inc bids asks trades tm with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    unfold doMatch
    repeat' (first | split | simp only [])
    all_goals
      first
        | exact Nat.le_refl _
        | exact ih _ _ _ _ _
        | exact Nat.le_trans (Nat.le_succ _) (ih _ _ _ _ _)

/-- `doMatch` only ever rewrites the contra side, so a buy incoming leaves the
    bids untouched. This is what keeps `SideFresh` alive across matching. -/
theorem doMatch_bids_of_buy (fuel : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp) (hside : inc.side = Side.buy) :
    (doMatch fuel inc bids asks trades tm).bids = bids := by
  induction fuel generalizing inc bids asks trades tm with
  | zero => rfl
  | succ n ih =>
    unfold doMatch
    simp only [hside]
    repeat' (first | split | simp only [])
    all_goals first | rfl | (apply ih; simp [hside])

/-- Mirror of `doMatch_bids_of_buy` for a sell incoming. -/
theorem doMatch_asks_of_sell (fuel : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp) (hside : inc.side = Side.sell) :
    (doMatch fuel inc bids asks trades tm).asks = asks := by
  induction fuel generalizing inc bids asks trades tm with
  | zero => rfl
  | succ n ih =>
    unfold doMatch
    simp only [hside]
    repeat' (first | split | simp only [])
    all_goals first | rfl | (apply ih; simp [hside])

/-- Matching never rewrites the incoming order's identity fields: it only
    decrements `remainingQty`/`visibleQty` and may set `status`. -/
theorem doMatch_incoming_side (fuel : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp) :
    (doMatch fuel inc bids asks trades tm).incoming.side = inc.side := by
  induction fuel generalizing inc bids asks trades tm with
  | zero => rfl
  | succ n ih =>
    unfold doMatch
    repeat' (first | split | simp only [])
    all_goals first | rfl | (rw [ih])

theorem doMatch_incoming_timestamp (fuel : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp) :
    (doMatch fuel inc bids asks trades tm).incoming.timestamp = inc.timestamp := by
  induction fuel generalizing inc bids asks trades tm with
  | zero => rfl
  | succ n ih =>
    unfold doMatch
    repeat' (first | split | simp only [])
    all_goals first | rfl | (rw [ih])

theorem doMatch_incoming_orderType (fuel : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp) :
    (doMatch fuel inc bids asks trades tm).incoming.orderType = inc.orderType := by
  induction fuel generalizing inc bids asks trades tm with
  | zero => rfl
  | succ n ih =>
    unfold doMatch
    repeat' (first | split | simp only [])
    all_goals first | rfl | (rw [ih])

theorem doMatch_incoming_tif (fuel : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp) :
    (doMatch fuel inc bids asks trades tm).incoming.tif = inc.tif := by
  induction fuel generalizing inc bids asks trades tm with
  | zero => rfl
  | succ n ih =>
    unfold doMatch
    repeat' (first | split | simp only [])
    all_goals first | rfl | (rw [ih])

-- ============================================================================
-- Preconditions for the processing pipeline
-- ============================================================================

/-- Well-formedness fragment the structural induction needs from an incoming
    order. Both clauses are implied by `Order.WellFormed`:

    * `0 < remainingQty` — WF-1 together with WF-11. A post-only order rests
      without matching, so nothing in the pipeline otherwise establishes it.
    * `postOnly → LIMIT` — WF-13. Phase 2 rests a post-only order directly, so
      it must not be a MARKET or MTL order.

    Nothing here restricts `minQty` on an MTL order. An earlier version of this
    file needed a third clause `MTL → minQty = none`, which `Order.WellFormed`
    does *not* imply, because `processOrder` handled the passing MinQty case in
    Phase 3b and so disposed an order whose type was still MARKET_TO_LIMIT.
    That was a mis-transcription of spec §12 (where Phase 3 is a fall-through
    guard); `Process.lean` now falls through, and the clause is gone. -/
def OrderRestOk (o : Order) : Prop :=
  0 < o.remainingQty ∧
  (o.postOnly = true → o.orderType = OrderType.limit)

/-- Invariant on the dormant stop list: it holds only genuine stop orders, each
    of which is fit to be processed once `convertStop` reactivates it.
    `convertStop` is the identity on non-stop order types, so without the first
    clause an MTL order parked in `.stops` would return as an MTL order. -/
def StopsWF (b : BookState) : Prop :=
  ∀ s ∈ b.stops,
    (s.orderType = OrderType.stopLimit ∨ s.orderType = OrderType.stopMarket) ∧
    0 < s.remainingQty ∧
    s.postOnly = false

theorem convertStop_side (s : Order) (t : Timestamp) : (convertStop s t).side = s.side := by
  unfold convertStop; split <;> rfl

theorem convertStop_remainingQty (s : Order) (t : Timestamp) :
    (convertStop s t).remainingQty = s.remainingQty := by
  unfold convertStop; split <;> rfl

theorem convertStop_postOnly (s : Order) (t : Timestamp) :
    (convertStop s t).postOnly = s.postOnly := by
  unfold convertStop; split <;> rfl

theorem convertStop_timestamp (s : Order) (t : Timestamp)
    (h : s.orderType = OrderType.stopLimit ∨ s.orderType = OrderType.stopMarket) :
    (convertStop s t).timestamp = t := by
  unfold convertStop
  rcases h with h | h <;> rw [h]

theorem convertStop_not_mtl (s : Order) (t : Timestamp)
    (h : s.orderType = OrderType.stopLimit ∨ s.orderType = OrderType.stopMarket) :
    (convertStop s t).orderType ≠ OrderType.marketToLimit := by
  unfold convertStop
  rcases h with h | h <;> rw [h] <;> intro hc <;> cases hc

/-- A stop order that satisfies `StopsWF`'s per-order conditions converts into
    an order the pipeline can process. -/
theorem convertStop_OrderRestOk (s : Order) (t : Timestamp)
    (hq : 0 < s.remainingQty) (hpo : s.postOnly = false) :
    OrderRestOk (convertStop s t) := by
  refine ⟨by rw [convertStop_remainingQty]; exact hq, ?_⟩
  intro hc; rw [convertStop_postOnly, hpo] at hc; cases hc

/-- The `max` in `processOrder`'s postcondition is only ever needed by the
    post-only branch; every other branch establishes the sharper `BookOk`. -/
theorem BookOkAt_max_of_BookOk {b : BookState} (t : Timestamp) (h : BookOk b) :
    BookOkAt (Nat.max b.clock (t + 1)) b := by
  unfold BookOk at h
  exact BookOkAt_mono (Nat.le_max_left b.clock (t + 1)) h

-- ============================================================================
-- Trade-event guarantees for `doMatch` (INV-11, INV-12)
-- ============================================================================

/-- A single emitted trade is safe: it was not initiated by a post-only
    order (INV-11) and it is not a self-trade (INV-12). -/
def TradeOk (t : Trade) : Prop :=
  t.aggPostOnly = false ∧
  ∀ g1 g2, t.aggStpGroup = some g1 → t.pasStpGroup = some g2 → g1 ≠ g2

def TradesOk (ts : List Trade) : Prop := ∀ t ∈ ts, TradeOk t

theorem TradesOk_nil : TradesOk [] := by intro t ht; cases ht

theorem TradesOk_append {ts : List Trade} {t : Trade}
    (hts : TradesOk ts) (ht : TradeOk t) : TradesOk (ts ++ [t]) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hts x h
  · rw [List.mem_singleton] at h; exact h ▸ ht

theorem TradesOk_append_list {ts us : List Trade}
    (hts : TradesOk ts) (hus : TradesOk us) : TradesOk (ts ++ us) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hts x h
  · exact hus x h

/-- The absence of an STP conflict is exactly the INV-12 obligation for the
    trade that the fill branch emits. -/
theorem stp_of_not_conflict {inc resting : Order}
    (h : ¬ (selfTradeConflict inc resting = true)) :
    ∀ g1 g2, inc.stpGroup = some g1 → resting.stpGroup = some g2 → g1 ≠ g2 := by
  intro g1 g2 h1 h2
  unfold selfTradeConflict at h
  rw [h1, h2] at h
  simpa using h

theorem doMatch_preserves_TradesOk (fuel : Nat) (inc : Order)
    (bids asks : List PriceLevel) (trades : List Trade) (tm : Timestamp)
    (hpo : inc.postOnly = false) (ht : TradesOk trades) :
    TradesOk (doMatch fuel inc bids asks trades tm).trades := by
  induction fuel generalizing inc bids asks trades tm with
  | zero => exact ht
  | succ n ih =>
    unfold doMatch
    repeat' (first | split | simp only [])
    all_goals
      first
        | exact ht
        | exact ih _ _ _ _ _ hpo ht
        | exact ih _ _ _ _ _ hpo
            (TradesOk_append ht ⟨hpo, stp_of_not_conflict (by assumption)⟩)
        | exact TradesOk_append ht ⟨hpo, stp_of_not_conflict (by assumption)⟩

-- ============================================================================
-- `insertOrder` preserves the structural bundle
-- ============================================================================

/-- The levels on an order's own side of the book (where it would rest). -/
def ownLevels (b : BookState) (s : Side) : List PriceLevel :=
  match s with
  | .buy  => b.bids
  | .sell => b.asks

/-- Every order already resting on `o`'s own side is strictly older than `o`.
    This is what makes back-of-queue insertion FIFO-safe. -/
def SideFresh (b : BookState) (o : Order) : Prop :=
  ∀ l ∈ ownLevels b o.side, ∀ x ∈ l.orders, x.timestamp < o.timestamp

theorem RestOk_of_mem_ownLevels {n : Timestamp} {b : BookState} {s : Side}
    {l : PriceLevel} {x : Order}
    (h : BookOkAt n b) (hl : l ∈ ownLevels b s) (hx : x ∈ l.orders) : x.timestamp < n := by
  cases s with
  | buy => exact ((h.1 l hl).2.2 x hx).2.2.2.2.2
  | sell => exact ((h.2 l hl).2.2 x hx).2.2.2.2.2

/-- An order stamped at or after the book's clock is newer than everything
    resting on it. This is how `SideFresh` is discharged at every call site:
    `process` stamps the incoming order with `b.clock`, and `convertStop`
    stamps a reactivated stop with the clock just before it is bumped. -/
theorem SideFresh_of_BookOk {b : BookState} {o : Order}
    (h : BookOk b) (hts : b.clock ≤ o.timestamp) : SideFresh b o :=
  fun _ hl _ hx => Nat.lt_of_lt_of_le (RestOk_of_mem_ownLevels h hl hx) hts

theorem insertDesc_SideOk {n : Timestamp} (levels : List PriceLevel) (o : Order) (p : Price)
    (h : SideOk n levels) (hok : RestOk n o)
    (hnew : ∀ l ∈ levels, ∀ x ∈ l.orders, x.timestamp < o.timestamp) :
    SideOk n (insertDesc levels o p) := by
  induction levels with
  | nil =>
    intro l hl
    rw [insertDesc, List.mem_singleton] at hl
    subst hl
    exact ⟨by simp, List.pairwise_singleton _ _, by
      intro x hx; rw [List.mem_singleton] at hx; exact hx ▸ hok⟩
  | cons lev rest ih =>
    unfold insertDesc
    split
    · exact SideOk_cons ⟨by simp, List.pairwise_singleton _ _, by
        intro x hx; rw [List.mem_singleton] at hx; exact hx ▸ hok⟩ h
    · split
      · refine SideOk_cons ⟨?_, ?_, ?_⟩ (SideOk_tail h)
        · simp
        · exact FIFOLevel_append_newest (SideOk_head h).2.1
            (hnew lev List.mem_cons_self)
        · intro x hx
          rcases List.mem_append.mp hx with hh | hh
          · exact (SideOk_head h).2.2 x hh
          · rw [List.mem_singleton] at hh; exact hh ▸ hok
      · exact SideOk_cons (SideOk_head h)
          (ih (SideOk_tail h) (fun l hl => hnew l (List.mem_cons_of_mem _ hl)))

theorem insertAsc_SideOk {n : Timestamp} (levels : List PriceLevel) (o : Order) (p : Price)
    (h : SideOk n levels) (hok : RestOk n o)
    (hnew : ∀ l ∈ levels, ∀ x ∈ l.orders, x.timestamp < o.timestamp) :
    SideOk n (insertAsc levels o p) := by
  induction levels with
  | nil =>
    intro l hl
    rw [insertAsc, List.mem_singleton] at hl
    subst hl
    exact ⟨by simp, List.pairwise_singleton _ _, by
      intro x hx; rw [List.mem_singleton] at hx; exact hx ▸ hok⟩
  | cons lev rest ih =>
    unfold insertAsc
    split
    · exact SideOk_cons ⟨by simp, List.pairwise_singleton _ _, by
        intro x hx; rw [List.mem_singleton] at hx; exact hx ▸ hok⟩ h
    · split
      · refine SideOk_cons ⟨?_, ?_, ?_⟩ (SideOk_tail h)
        · simp
        · exact FIFOLevel_append_newest (SideOk_head h).2.1
            (hnew lev List.mem_cons_self)
        · intro x hx
          rcases List.mem_append.mp hx with hh | hh
          · exact (SideOk_head h).2.2 x hh
          · rw [List.mem_singleton] at hh; exact hh ▸ hok
      · exact SideOk_cons (SideOk_head h)
          (ih (SideOk_tail h) (fun l hl => hnew l (List.mem_cons_of_mem _ hl)))

/-- `insertOrder` preserves the structural bundle. Note that `insertOrder`
    itself clears `minQty` (INV-14) and sets a resting status (INV-6), so the
    only obligations on `o` are INV-5, INV-8, INV-13 and the timestamp bound. -/
theorem insertOrder_BookOkAt (b : BookState) (o : Order) (hasTrades : Bool) (n : Timestamp)
    (h : BookOkAt n b) (hfresh : SideFresh b o)
    (hq : 0 < o.remainingQty) (hmk : o.orderType ≠ OrderType.market)
    (hmtl : o.orderType ≠ OrderType.marketToLimit) (hts : o.timestamp < n) :
    BookOkAt n (insertOrder b o hasTrades) := by
  have hok : RestOk n { o with
      visibleQty := match o.displayQty with
        | some d => min d o.remainingQty
        | none => o.remainingQty,
      status := if hasTrades then OrderStatus.partiallyFilled else OrderStatus.new_,
      minQty := none } := by
    refine ⟨hq, ?_, hmk, hmtl, rfl, hts⟩
    cases hasTrades
    · exact Or.inl rfl
    · exact Or.inr rfl
  unfold insertOrder
  unfold SideFresh ownLevels at hfresh
  cases hside : o.side with
  | buy =>
    rw [hside] at hfresh
    exact ⟨insertDesc_SideOk b.bids _ _ h.1 hok hfresh, h.2⟩
  | sell =>
    rw [hside] at hfresh
    exact ⟨h.1, insertAsc_SideOk b.asks _ _ h.2 hok hfresh⟩

theorem StopsWF_of_same_stops (b b' : BookState) (h : b'.stops = b.stops)
    (hs : StopsWF b) : StopsWF b' := by
  intro s hm; rw [h] at hm; exact hs s hm

-- ============================================================================
-- Clock monotonicity for the processing pipeline
-- ============================================================================

theorem insertOrder_clock (b : BookState) (o : Order) (hasTrades : Bool) :
    (insertOrder b o hasTrades).clock = b.clock := by
  unfold insertOrder
  cases o.side <;> rfl

theorem dispose_clock (inc : Order) (b : BookState) (trades : List Trade) :
    (dispose inc b trades).clock = b.clock := by
  unfold dispose
  split
  · rfl
  split
  · rfl
  split
  · rfl
  exact insertOrder_clock _ _ _

theorem le_insertOrder_clock {n : Timestamp} (b : BookState) (o : Order) (hasTrades : Bool)
    (h : n ≤ b.clock) : n ≤ (insertOrder b o hasTrades).clock := by
  rw [insertOrder_clock]; exact h

theorem le_dispose_clock {n : Timestamp} (inc : Order) (b : BookState) (trades : List Trade)
    (h : n ≤ b.clock) : n ≤ (dispose inc b trades).clock := by
  rw [dispose_clock]; exact h

/-- `matchOrder` starts the match loop at `b.clock + 1`, so its result clock is
    strictly above the book clock. This is what lets a freshly stamped incoming
    order (timestamp `b.clock`) rest without breaking the `RestOk` bound. -/
theorem matchOrder_clock_gt (b : BookState) (o : Order) (fuel : Nat) :
    b.clock < (matchOrder fuel b o).clock := by
  unfold matchOrder
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (doMatch_clock_ge _ _ _ _ _ _)

/-- The pipeline clock never runs backwards. Needed to show that the bound
    carried by `BookOkAt` can always be taken to be the *result* clock. -/
theorem process_all_clock_ge : ∀ (fuel : Nat),
    (∀ (o : Order) (b : BookState),
      b.clock ≤ (processOrder fuel o b).book.clock) ∧
    (∀ (trades : List Trade) (b : BookState),
      b.clock ≤ (processCascade fuel trades b).book.clock) ∧
    (∀ (orders : List Order) (b : BookState),
      b.clock ≤ (processTriggeredStops fuel orders b).book.clock) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun _ _ => Nat.le_refl _, ?_, ?_⟩
    · intro ts b; cases ts <;> exact Nat.le_refl _
    · intro os b; cases os <;> exact Nat.le_refl _
  | succ n ih =>
    obtain ⟨ih_po, ih_pc, ih_pts⟩ := ih
    -- Transitivity-shaped forms of the IHs: stating them this way lets the
    -- unifier fix the book argument from the goal before the `≤` side
    -- condition is checked, which plain `ih_pc _ _` cannot do.
    have hpo : ∀ (m : Timestamp) (oo : Order) (bb : BookState),
        m ≤ bb.clock → m ≤ (processOrder n oo bb).book.clock :=
      fun m oo bb h => Nat.le_trans h (ih_po oo bb)
    have hpc : ∀ (m : Timestamp) (ts : List Trade) (bb : BookState),
        m ≤ bb.clock → m ≤ (processCascade n ts bb).book.clock :=
      fun m ts bb h => Nat.le_trans h (ih_pc ts bb)
    refine ⟨?_, ?_, ?_⟩
    · intro o b
      unfold processOrder
      simp only
      repeat' (first | split | simp only [])
      all_goals
        first
          | exact Nat.le_refl _
          | exact hpo _ _ _ (Nat.le_succ _)
          | exact le_insertOrder_clock _ _ _ (Nat.le_refl _)
          | exact Nat.le_of_lt (matchOrder_clock_gt _ _ _)
          | exact hpc _ _ _ (Nat.le_of_lt (matchOrder_clock_gt _ _ _))
          | exact hpc _ _ _
              (le_dispose_clock _ _ _ (Nat.le_of_lt (matchOrder_clock_gt _ _ _)))
          | exact hpc _ _ _
              (Nat.le_trans (Nat.le_of_lt (matchOrder_clock_gt _ _ _))
                (doMatch_clock_ge _ _ _ _ _ _))
          | exact hpc _ _ _
              (le_dispose_clock _ _ _
                (Nat.le_trans (Nat.le_of_lt (matchOrder_clock_gt _ _ _))
                  (doMatch_clock_ge _ _ _ _ _ _)))
    · intro ts b
      cases ts with
      | nil => exact Nat.le_refl _
      | cons t rest =>
        unfold processCascade
        simp only
        split
        · exact ih_pc rest { b with lastTradePrice := some t.price }
        · exact Nat.le_trans
            (ih_pts _ { b with
              stops := (b.stops.partition (fun s => shouldTrigger s (some t.price))).2,
              lastTradePrice := some t.price })
            (ih_pc rest _)
    · intro os b
      cases os with
      | nil => exact Nat.le_refl _
      | cons stop rest =>
        unfold processTriggeredStops
        simp only
        exact Nat.le_trans
          (Nat.le_trans (Nat.le_succ b.clock)
            (ih_po (convertStop stop b.clock) { b with clock := b.clock + 1 }))
          (ih_pts rest _)

theorem processOrder_clock_ge (fuel : Nat) (o : Order) (b : BookState) :
    b.clock ≤ (processOrder fuel o b).book.clock := (process_all_clock_ge fuel).1 o b

theorem processCascade_clock_ge (fuel : Nat) (trades : List Trade) (b : BookState) :
    b.clock ≤ (processCascade fuel trades b).book.clock := (process_all_clock_ge fuel).2.1 trades b

theorem processTriggeredStops_clock_ge (fuel : Nat) (orders : List Order) (b : BookState) :
    b.clock ≤ (processTriggeredStops fuel orders b).book.clock :=
  (process_all_clock_ge fuel).2.2 orders b

-- ============================================================================
-- `dispose` preserves the structural bundle
-- ============================================================================

/-- `BookOkAt` only looks at the two order books, so any state update that
    leaves `bids`/`asks` alone (clock, stops, lastTradePrice, nextId) is free. -/
theorem BookOkAt_congr {n : Timestamp} {b b' : BookState}
    (hb : b'.bids = b.bids) (ha : b'.asks = b.asks) (h : BookOkAt n b) : BookOkAt n b' := by
  unfold BookOkAt; rw [hb, ha]; exact h

theorem SideFresh_congr {b b' : BookState} {o o' : Order}
    (hts : o'.timestamp = o.timestamp)
    (hown : ownLevels b' o'.side = ownLevels b o.side)
    (h : SideFresh b o) : SideFresh b' o' := by
  intro l hl x hx
  rw [hts]
  exact h l (by rw [← hown]; exact hl) x hx

/-- The book resulting from a match: contra side rewritten, own side intact. -/
def matchedBook (b : BookState) (o : Order) (fuel : Nat) : BookState :=
  { b with
    bids := (matchOrder fuel b o).bids,
    asks := (matchOrder fuel b o).asks,
    clock := (matchOrder fuel b o).clock }

/-- Matching preserves the structural bundle, at the *post-match* clock. This
    is the `doMatch` theorem lifted through `matchOrder`'s `b.clock + 1` start. -/
theorem matchedBook_BookOk (b : BookState) (o : Order) (fuel : Nat) (h : BookOk b) :
    BookOk (matchedBook b o fuel) := by
  have h' : SideOk (b.clock + 1) b.bids ∧ SideOk (b.clock + 1) b.asks :=
    BookOkAt_mono (Nat.le_succ _) h
  unfold matchedBook BookOk BookOkAt matchOrder
  exact doMatch_preserves_SideOk fuel o b.bids b.asks [] (b.clock + 1) h'.1 h'.2

/-- `doMatch` never touches the incoming order's own side, so a freshness
    witness for the incoming survives matching unchanged. -/
theorem SideFresh_matchedBook (b : BookState) (o : Order) (fuel : Nat)
    (h : SideFresh b o) :
    SideFresh (matchedBook b o fuel) (matchOrder fuel b o).incoming := by
  have hside : (matchOrder fuel b o).incoming.side = o.side := by
    unfold matchOrder; exact doMatch_incoming_side _ _ _ _ _ _
  have hts : (matchOrder fuel b o).incoming.timestamp = o.timestamp := by
    unfold matchOrder; exact doMatch_incoming_timestamp _ _ _ _ _ _
  refine SideFresh_congr hts ?_ h
  rw [hside]
  cases hs : o.side with
  | buy =>
    simp only [ownLevels]
    unfold matchedBook matchOrder
    exact doMatch_bids_of_buy _ _ _ _ _ _ hs
  | sell =>
    simp only [ownLevels]
    unfold matchedBook matchOrder
    exact doMatch_asks_of_sell _ _ _ _ _ _ hs

/-- `dispose` preserves the structural bundle. The `remainingQty > 0` (INV-5)
    and `orderType ≠ MARKET` (INV-8) obligations are discharged by `dispose`'s
    own guards; INV-13 must come from the caller (the MTL phase converts the
    order to a LIMIT before disposing). -/
theorem dispose_BookOkAt (inc : Order) (b : BookState) (trades : List Trade) (n : Timestamp)
    (h : BookOkAt n b) (hfresh : SideFresh b inc)
    (hmtl : inc.orderType ≠ OrderType.marketToLimit) (hts : inc.timestamp < n) :
    BookOkAt n (dispose inc b trades) := by
  unfold dispose
  split
  · exact h
  · split
    · exact h
    · split
      · exact h
      · rename_i hnz _ hmk
        refine insertOrder_BookOkAt b inc _ n h hfresh ?_ ?_ hmtl hts
        · have : ¬ (inc.remainingQty == 0) = true := by
            intro hc; exact hnz (by simp [hc])
          exact Nat.pos_of_ne_zero (by simpa using this)
        · intro hc; exact hmk (by rw [hc]; rfl)

-- ============================================================================
-- Phase-level packaging for the mutual induction
-- ============================================================================

/-- Post-only insertion (Phase 2) is the one branch that rests an order without
    the clock having advanced, so it is the only reason `processOrder`'s
    postcondition carries a `max` rather than plain `BookOk`. -/
theorem insertOrder_BookOkAt_max (b : BookState) (o : Order) (hasTrades : Bool)
    (h : BookOk b) (hfresh : SideFresh b o) (hq : 0 < o.remainingQty)
    (hmk : o.orderType ≠ OrderType.market) (hmtl : o.orderType ≠ OrderType.marketToLimit) :
    BookOkAt (Nat.max (insertOrder b o hasTrades).clock (o.timestamp + 1))
      (insertOrder b o hasTrades) := by
  rw [insertOrder_clock]
  unfold BookOk at h
  refine insertOrder_BookOkAt b o hasTrades _ ?_ hfresh hq hmk hmtl ?_
  · exact BookOkAt_mono (Nat.le_max_left _ _) h
  · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)

/-- Disposition after matching. The incoming order is stamped before the match
    starts and `matchOrder` runs the clock forward from `b.clock + 1`, so the
    residual is always strictly older than the post-match clock — which is what
    lets it join the back of its queue without breaking FIFO. -/
theorem disposed_BookOk (b : BookState) (o : Order) (fuel : Nat) (inc : Order)
    (trades : List Trade)
    (hb : BookOk b) (hfresh : SideFresh b o)
    (hside : inc.side = o.side) (hts : inc.timestamp = o.timestamp)
    (hmtl : inc.orderType ≠ OrderType.marketToLimit)
    (hle : o.timestamp ≤ b.clock) :
    BookOk (dispose inc (matchedBook b o fuel) trades) := by
  have hmb : BookOk (matchedBook b o fuel) := matchedBook_BookOk b o fuel hb
  have hincts : (matchOrder fuel b o).incoming.timestamp = o.timestamp := by
    unfold matchOrder; exact doMatch_incoming_timestamp _ _ _ _ _ _
  have hincside : (matchOrder fuel b o).incoming.side = o.side := by
    unfold matchOrder; exact doMatch_incoming_side _ _ _ _ _ _
  have hfr : SideFresh (matchedBook b o fuel) inc := by
    refine SideFresh_congr (b := matchedBook b o fuel)
      (o := (matchOrder fuel b o).incoming) ?_ ?_ (SideFresh_matchedBook b o fuel hfresh)
    · rw [hts, hincts]
    · rw [hside, hincside]
  have hclock : o.timestamp < (matchedBook b o fuel).clock := by
    show o.timestamp < (matchOrder fuel b o).clock
    exact Nat.lt_of_le_of_lt hle (matchOrder_clock_gt b o fuel)
  unfold BookOk
  rw [dispose_clock]
  exact dispose_BookOkAt inc (matchedBook b o fuel) trades _ hmb hfr hmtl (by rw [hts]; exact hclock)

/-- Every phase that ends in a stop cascade closes the same way: establish the
    bundle for the book handed to the cascade, then let the induction hypothesis
    carry it through. The `max` collapses because the cascade never rewinds the
    clock. -/
theorem cascade_step {n : Nat} {bb : BookState} {t : Timestamp} {ts : List Trade}
    (ih : ∀ (ts : List Trade) (bb : BookState), BookOk bb → StopsWF bb →
      BookOk (processCascade n ts bb).book ∧ StopsWF (processCascade n ts bb).book)
    (h1 : BookOk bb) (h2 : StopsWF bb) :
    BookOkAt (Nat.max (processCascade n ts bb).book.clock (t + 1))
      (processCascade n ts bb).book ∧ StopsWF (processCascade n ts bb).book :=
  ⟨BookOkAt_max_of_BookOk t (ih ts bb h1 h2).1, (ih ts bb h1 h2).2⟩

/-- `Nat.max` phrased so that `rw` can use it: the ambient `max` from the
    `Max Nat` instance is defeq but not syntactically equal. -/
theorem nat_max_eq_left {a c : Nat} (h : c ≤ a) : Nat.max a c = a := Nat.max_eq_left h

theorem mem_partition_snd {a : Type} (l : List a) (p : a -> Bool) (x : a)
    (h : x ∈ (l.partition p).2) : x ∈ l := by
  rw [List.partition_eq_filter_filter] at h
  exact (List.mem_filter.mp h).1

theorem mem_partition_fst {a : Type} (l : List a) (p : a -> Bool) (x : a)
    (h : x ∈ (l.partition p).1) : x ∈ l := by
  rw [List.partition_eq_filter_filter] at h
  exact (List.mem_filter.mp h).1

/-- Generic "match, then dispose the residual" step, with the match resuming at
    the book's own clock. This is the MTL second pass (§9): the first pass has
    already advanced the clock past the incoming order's timestamp, so the
    strictness needed for FIFO comes from `hlt` rather than from a `+ 1`. -/
theorem match_dispose_BookOk (bb : BookState) (inc : Order) (fuel : Nat)
    (trades : List Trade)
    (hb : BookOk bb) (hfresh : SideFresh bb inc)
    (hmtl : inc.orderType ≠ OrderType.marketToLimit)
    (hlt : inc.timestamp < bb.clock) :
    BookOk (dispose (doMatch fuel inc bb.bids bb.asks [] bb.clock).incoming
      { bb with bids := (doMatch fuel inc bb.bids bb.asks [] bb.clock).bids,
                asks := (doMatch fuel inc bb.bids bb.asks [] bb.clock).asks,
                clock := (doMatch fuel inc bb.bids bb.asks [] bb.clock).clock }
      trades) := by
  have hmr : BookOkAt (doMatch fuel inc bb.bids bb.asks [] bb.clock).clock
      { bb with bids := (doMatch fuel inc bb.bids bb.asks [] bb.clock).bids,
                asks := (doMatch fuel inc bb.bids bb.asks [] bb.clock).asks,
                clock := (doMatch fuel inc bb.bids bb.asks [] bb.clock).clock } :=
    doMatch_preserves_SideOk fuel inc bb.bids bb.asks [] bb.clock hb.1 hb.2
  have hts : (doMatch fuel inc bb.bids bb.asks [] bb.clock).incoming.timestamp = inc.timestamp :=
    doMatch_incoming_timestamp _ _ _ _ _ _
  have hside : (doMatch fuel inc bb.bids bb.asks [] bb.clock).incoming.side = inc.side :=
    doMatch_incoming_side _ _ _ _ _ _
  have hfr : SideFresh
      { bb with bids := (doMatch fuel inc bb.bids bb.asks [] bb.clock).bids,
                asks := (doMatch fuel inc bb.bids bb.asks [] bb.clock).asks,
                clock := (doMatch fuel inc bb.bids bb.asks [] bb.clock).clock }
      (doMatch fuel inc bb.bids bb.asks [] bb.clock).incoming := by
    refine SideFresh_congr hts ?_ hfresh
    rw [hside]
    cases hs : inc.side with
    | buy => simp only [ownLevels]; exact doMatch_bids_of_buy _ _ _ _ _ _ hs
    | sell => simp only [ownLevels]; exact doMatch_asks_of_sell _ _ _ _ _ _ hs
  have hmtl2 : (doMatch fuel inc bb.bids bb.asks [] bb.clock).incoming.orderType
      ≠ OrderType.marketToLimit := by
    rw [doMatch_incoming_orderType]; exact hmtl
  have hclock : bb.clock ≤ (doMatch fuel inc bb.bids bb.asks [] bb.clock).clock :=
    doMatch_clock_ge _ _ _ _ _ _
  unfold BookOk
  rw [dispose_clock]
  refine dispose_BookOkAt _ _ trades _ hmr hfr hmtl2 ?_
  rw [hts]
  exact Nat.lt_of_lt_of_le hlt hclock

-- ============================================================================
-- Main mutual induction: the pipeline preserves the structural bundle
-- ============================================================================

theorem process_all_BookOk : ∀ (fuel : Nat),
    (∀ (o : Order) (b : BookState),
      BookOk b → StopsWF b → OrderRestOk o → SideFresh b o → o.timestamp ≤ b.clock →
      BookOkAt (Nat.max (processOrder fuel o b).book.clock (o.timestamp + 1))
        (processOrder fuel o b).book ∧
      StopsWF (processOrder fuel o b).book) ∧
    (∀ (trades : List Trade) (b : BookState),
      BookOk b → StopsWF b →
      BookOk (processCascade fuel trades b).book ∧
      StopsWF (processCascade fuel trades b).book) ∧
    (∀ (orders : List Order) (b : BookState),
      BookOk b → StopsWF b →
      (∀ s ∈ orders,
        (s.orderType = OrderType.stopLimit ∨ s.orderType = OrderType.stopMarket) ∧
        0 < s.remainingQty ∧ s.postOnly = false) →
      BookOk (processTriggeredStops fuel orders b).book ∧
      StopsWF (processTriggeredStops fuel orders b).book) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro o b hb hs _ _ _
      exact ⟨BookOkAt_max_of_BookOk _ hb, hs⟩
    · intro ts b hb hs; cases ts <;> exact ⟨hb, hs⟩
    · intro os b hb hs _; cases os <;> exact ⟨hb, hs⟩
  | succ n ih =>
    obtain ⟨ih_po, ih_pc, ih_pts⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · -- ------------------------------------------------------------------
      -- processOrder
      -- ------------------------------------------------------------------
      intro o b hb hstops hok hfresh hle
      unfold processOrder
      simp only
      split
      · -- Phase 1 (§10): stop order
        rename_i hstop
        have ho_stop : o.orderType = OrderType.stopLimit ∨ o.orderType = OrderType.stopMarket := by
          rw [Bool.or_eq_true] at hstop
          rcases hstop with h1 | h2
          · left; cases hv : o.orderType <;> rw [hv] at h1 <;> first | rfl | cases h1
          · right; cases hv : o.orderType <;> rw [hv] at h2 <;> first | rfl | cases h2
        have hopo : o.postOnly = false := by
          cases hpv : o.postOnly with
          | false => rfl
          | true =>
            have hl := hok.2 hpv
            rcases ho_stop with hh | hh <;> (rw [hl] at hh; cases hh)
        split
        · -- triggered: convert with a fresh stamp, bump the clock, reprocess
          have hconv : OrderRestOk (convertStop o b.clock) :=
            convertStop_OrderRestOk o b.clock hok.1 hopo
          have hcts : (convertStop o b.clock).timestamp = b.clock :=
            convertStop_timestamp o b.clock ho_stop
          have hb' : BookOk { b with clock := b.clock + 1 } :=
            BookOkAt_mono (Nat.le_succ _) hb
          have hfr : SideFresh { b with clock := b.clock + 1 } (convertStop o b.clock) := by
            intro l hl x hx
            rw [hcts]
            exact RestOk_of_mem_ownLevels hb hl hx
          have hle' : (convertStop o b.clock).timestamp
              ≤ ({ b with clock := b.clock + 1 } : BookState).clock := by
            rw [hcts]; exact Nat.le_succ _
          obtain ⟨hbk, hst⟩ := ih_po (convertStop o b.clock) { b with clock := b.clock + 1 }
            hb' hstops hconv hfr hle'
          refine ⟨?_, hst⟩
          have hR : b.clock + 1
              ≤ (processOrder n (convertStop o b.clock)
                  { b with clock := b.clock + 1 }).book.clock :=
            processOrder_clock_ge n (convertStop o b.clock) { b with clock := b.clock + 1 }
          rw [hcts, nat_max_eq_left hR] at hbk
          exact BookOkAt_mono (Nat.le_max_left _ _) hbk
        · -- not triggered: park on the dormant stop list
          refine ⟨BookOkAt_max_of_BookOk _ hb, ?_⟩
          intro s hs
          rw [List.mem_append] at hs
          rcases hs with hm | hm
          · exact hstops s hm
          · rw [List.mem_singleton] at hm
            exact hm ▸ ⟨ho_stop, hok.1, hopo⟩
      · split
        · -- Phase 2 (§7.6): post-only, REJECT policy
          rename_i _ hpo
          have hpov : o.postOnly = true := by
            cases hpv : o.postOnly with
            | true => rfl
            | false => rw [hpv] at hpo; cases hpo
          have hlim : o.orderType = OrderType.limit := hok.2 hpov
          split
          · exact ⟨BookOkAt_max_of_BookOk _ hb, hstops⟩
          · refine ⟨insertOrder_BookOkAt_max b o false hb hfresh hok.1 ?_ ?_, ?_⟩
            · rw [hlim]; intro hc; cases hc
            · rw [hlim]; intro hc; cases hc
            · exact StopsWF_of_same_stops b _ (insertOrder_preserves_stops b o false) hstops
        · split
          · -- Phase 3 (§5.3): FOK. Either rejected, or fully filled — never rests.
            split
            · exact ⟨BookOkAt_max_of_BookOk _ hb, hstops⟩
            · refine cascade_step ih_pc ?_ ?_
              · exact BookOkAt_congr rfl rfl (matchedBook_BookOk b o _ hb)
              · exact StopsWF_of_same_stops b _ rfl hstops
          · split
            · -- Phase 3b (§5.4): MinQty pre-check failed — order rejected,
              -- book untouched. A *passing* order does not land here: it falls
              -- through to MTL routing or normal matching, both of which clear
              -- minQty before anything can rest. That fall-through is what
              -- keeps INV-13 provable without an extra precondition.
              exact ⟨BookOkAt_max_of_BookOk _ hb, hstops⟩
            · split
              · -- Phase 4 (§9): MTL routing
                split
                · -- no trades: nothing rests, book is just the matched book
                  exact ⟨BookOkAt_max_of_BookOk _
                    (BookOkAt_congr rfl rfl (matchedBook_BookOk b o _ hb)),
                    StopsWF_of_same_stops b _ rfl hstops⟩
                · split
                  · -- converted remainder is zero: cascade over the matched book
                    refine cascade_step ih_pc ?_ ?_
                    · exact BookOkAt_congr rfl rfl (matchedBook_BookOk b o _ hb)
                    · exact StopsWF_of_same_stops b _ rfl hstops
                  · -- second matching pass, then dispose the converted LIMIT
                    refine cascade_step ih_pc ?_ ?_
                    · have h1 : (matchOrder (computeMatchFuel b o.side) b o).incoming.timestamp
                          = o.timestamp := by
                        unfold matchOrder; exact doMatch_incoming_timestamp _ _ _ _ _ _
                      have h2 := matchOrder_clock_gt b o (computeMatchFuel b o.side)
                      have h3 : (matchOrder (computeMatchFuel b o.side) b o).incoming.timestamp
                          < (matchOrder (computeMatchFuel b o.side) b o).clock := by
                        rw [h1]; exact Nat.lt_of_le_of_lt hle h2
                      refine BookOkAt_congr rfl rfl
                        (match_dispose_BookOk _ _ _ _ (matchedBook_BookOk b o _ hb) ?_ ?_ h3)
                      · exact SideFresh_congr rfl rfl (SideFresh_matchedBook b o _ hfresh)
                      · intro hc; cases hc
                    · exact StopsWF_of_same_stops b _ (dispose_preserves_stops _ _ _) hstops
              · -- Phase 5 (§5.1): normal matching
                rename_i _ _ _ _ hmtlb
                refine cascade_step ih_pc ?_ ?_
                · refine BookOkAt_congr rfl rfl
                    (disposed_BookOk b o _ _ _ hb hfresh ?_ ?_ ?_ hle)
                  · split <;> (unfold matchOrder; exact doMatch_incoming_side _ _ _ _ _ _)
                  · split <;> (unfold matchOrder; exact doMatch_incoming_timestamp _ _ _ _ _ _)
                  · intro hc
                    have hoT : o.orderType = OrderType.marketToLimit := by
                      rw [← hc]
                      split <;>
                        (unfold matchOrder
                         exact (doMatch_incoming_orderType _ _ _ _ _ _).symm)
                    exact hmtlb (by rw [hoT]; rfl)
                · exact StopsWF_of_same_stops b _ (dispose_preserves_stops _ _ _) hstops
    · -- ------------------------------------------------------------------
      -- processCascade
      -- ------------------------------------------------------------------
      intro ts b hb hstops
      cases ts with
      | nil => exact ⟨hb, hstops⟩
      | cons t rest =>
        unfold processCascade
        simp only
        split
        · exact ih_pc rest { b with lastTradePrice := some t.price } hb hstops
        · refine ih_pc rest _ ?_ ?_
          · exact (ih_pts _ { b with
              stops := (b.stops.partition (fun s => shouldTrigger s (some t.price))).2,
              lastTradePrice := some t.price } hb
              (fun s hs => hstops s (mem_partition_snd _ _ s hs))
              (fun s hs => hstops s (mem_partition_fst _ _ s
                (List.mem_mergeSort.mp hs)))).1
          · exact (ih_pts _ { b with
              stops := (b.stops.partition (fun s => shouldTrigger s (some t.price))).2,
              lastTradePrice := some t.price } hb
              (fun s hs => hstops s (mem_partition_snd _ _ s hs))
              (fun s hs => hstops s (mem_partition_fst _ _ s
                (List.mem_mergeSort.mp hs)))).2
    · -- ------------------------------------------------------------------
      -- processTriggeredStops
      -- ------------------------------------------------------------------
      intro os b hb hstops horders
      cases os with
      | nil => exact ⟨hb, hstops⟩
      | cons stop rest =>
        unfold processTriggeredStops
        simp only
        have hs0 := horders stop List.mem_cons_self
        have hconv : OrderRestOk (convertStop stop b.clock) :=
          convertStop_OrderRestOk stop b.clock hs0.2.1 hs0.2.2
        have hcts : (convertStop stop b.clock).timestamp = b.clock :=
          convertStop_timestamp stop b.clock hs0.1
        have hb' : BookOk { b with clock := b.clock + 1 } :=
          BookOkAt_mono (Nat.le_succ _) hb
        have hfr : SideFresh { b with clock := b.clock + 1 } (convertStop stop b.clock) := by
          intro l hl x hx
          rw [hcts]
          exact RestOk_of_mem_ownLevels hb hl hx
        have hle' : (convertStop stop b.clock).timestamp
            ≤ ({ b with clock := b.clock + 1 } : BookState).clock := by
          rw [hcts]; exact Nat.le_succ _
        obtain ⟨hbk, hst⟩ := ih_po (convertStop stop b.clock) { b with clock := b.clock + 1 }
          hb' hstops hconv hfr hle'
        have hR : b.clock + 1
            ≤ (processOrder n (convertStop stop b.clock)
                { b with clock := b.clock + 1 }).book.clock :=
          processOrder_clock_ge n (convertStop stop b.clock) { b with clock := b.clock + 1 }
        rw [hcts, nat_max_eq_left hR] at hbk
        exact ih_pts rest _ hbk hst (fun s hs => horders s (List.mem_cons_of_mem _ hs))

-- ============================================================================
-- Projecting the bundle onto the named §13 invariants
-- ============================================================================

/-- The book-state half of the §13 suite. The trade-event guarantees INV-11 and
    INV-12 are deliberately *not* folded in: the final book state does not
    retain the emitted trades, so they are proved separately below. -/
def FullBookInv (b : BookState) : Prop :=
  NoEmptyLevels b ∧ NoGhosts b ∧ StatusConsistency b ∧ FIFOWithinLevel b ∧
  NoRestingMarkets b ∧ NoRestingMTL b ∧ NoRestingMinQty b

theorem FullBookInv_of_BookOkAt {n : Timestamp} {b : BookState} (h : BookOkAt n b) :
    FullBookInv b :=
  ⟨⟨fun l hl => (h.1 l hl).1, fun l hl => (h.2 l hl).1⟩,
   ⟨fun l hl o ho => ((h.1 l hl).2.2 o ho).1,
    fun l hl o ho => ((h.2 l hl).2.2 o ho).1⟩,
   ⟨fun l hl o ho => ((h.1 l hl).2.2 o ho).2.1,
    fun l hl o ho => ((h.2 l hl).2.2 o ho).2.1⟩,
   ⟨fun l hl => (h.1 l hl).2.1, fun l hl => (h.2 l hl).2.1⟩,
   ⟨fun l hl o ho => ((h.1 l hl).2.2 o ho).2.2.1,
    fun l hl o ho => ((h.2 l hl).2.2 o ho).2.2.1⟩,
   ⟨fun l hl o ho => ((h.1 l hl).2.2 o ho).2.2.2.1,
    fun l hl o ho => ((h.2 l hl).2.2 o ho).2.2.2.1⟩,
   ⟨fun l hl o ho => ((h.1 l hl).2.2 o ho).2.2.2.2.1,
    fun l hl o ho => ((h.2 l hl).2.2 o ho).2.2.2.2.1⟩⟩

-- ============================================================================
-- Trade-event guarantees for the whole pipeline (INV-11, INV-12)
-- ============================================================================

theorem doMatch_incoming_postOnly (fuel : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp) :
    (doMatch fuel inc bids asks trades tm).incoming.postOnly = inc.postOnly := by
  induction fuel generalizing inc bids asks trades tm with
  | zero => rfl
  | succ n ih =>
    unfold doMatch
    repeat' (first | split | simp only [])
    all_goals first | rfl | (rw [ih])

/-- No precondition is needed: an order only reaches a matching phase after
    failing the Phase 2 post-only test, so `aggPostOnly` is false on every
    emitted trade by construction (INV-11), and the STP branches never emit a
    trade between two orders of the same group (INV-12). -/
theorem process_all_TradesOk : ∀ (fuel : Nat),
    (∀ (o : Order) (b : BookState), TradesOk (processOrder fuel o b).trades) ∧
    (∀ (trades : List Trade) (b : BookState), TradesOk (processCascade fuel trades b).trades) ∧
    (∀ (orders : List Order) (b : BookState),
      TradesOk (processTriggeredStops fuel orders b).trades) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun _ _ => TradesOk_nil, ?_, ?_⟩
    · intro ts _; cases ts <;> exact TradesOk_nil
    · intro os _; cases os <;> exact TradesOk_nil
  | succ n ih =>
    obtain ⟨ih_po, ih_pc, ih_pts⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro o b
      unfold processOrder
      simp only
      split
      · split
        · exact ih_po _ _
        · exact TradesOk_nil
      · split
        · split
          · exact TradesOk_nil
          · exact TradesOk_nil
        · -- past Phase 2, so the incoming is not post-only
          rename_i _ hpo
          have hpof : o.postOnly = false := by
            cases hpv : o.postOnly with
            | false => rfl
            | true => rw [hpv] at hpo; exact absurd rfl hpo
          have hmt : ∀ (fuel' : Nat),
              TradesOk (matchOrder fuel' b o).trades := by
            intro fuel'
            unfold matchOrder
            exact doMatch_preserves_TradesOk _ _ _ _ _ _ hpof TradesOk_nil
          split
          · split
            · exact TradesOk_nil
            · exact TradesOk_append_list (hmt _) (ih_pc _ _)
          · split
            · exact TradesOk_nil
            · split
              · split
                · exact TradesOk_nil
                · split
                  · exact TradesOk_append_list (hmt _) (ih_pc _ _)
                  · refine TradesOk_append_list (TradesOk_append_list (hmt _) ?_) (ih_pc _ _)
                    refine doMatch_preserves_TradesOk _ _ _ _ _ _ ?_ TradesOk_nil
                    show (matchOrder (computeMatchFuel b o.side) b o).incoming.postOnly = false
                    unfold matchOrder
                    rw [doMatch_incoming_postOnly]; exact hpof
              · exact TradesOk_append_list (hmt _) (ih_pc _ _)
    · intro ts b
      cases ts with
      | nil => exact TradesOk_nil
      | cons t rest =>
        unfold processCascade
        simp only
        split
        · exact ih_pc _ _
        · exact TradesOk_append_list (ih_pts _ _) (ih_pc _ _)
    · intro os b
      cases os with
      | nil => exact TradesOk_nil
      | cons stop rest =>
        unfold processTriggeredStops
        simp only
        exact TradesOk_append_list (ih_po _ _) (ih_pts _ _)

-- ============================================================================
-- Top-level results for `process`
-- ============================================================================

/-- `process` stamps the incoming order with `b.clock` and, on the way out,
    advances the clock to at least `b.clock + 1`. That final bump is exactly
    what discharges the `max` in `processOrder`'s postcondition: it is the only
    thing separating a freshly rested post-only order from the book clock. -/
theorem process_preserves_BookOk (b : BookState) (o : Order)
    (hb : BookOk b) (hstops : StopsWF b) (hok : OrderRestOk o) :
    BookOk (process b o).book ∧ StopsWF (process b o).book := by
  unfold process
  obtain ⟨hbk, hst⟩ := (process_all_BookOk defaultFuel).1
    { o with id := b.nextId, timestamp := b.clock } b hb hstops hok
    (SideFresh_of_BookOk hb (Nat.le_refl _)) (Nat.le_refl _)
  exact ⟨BookOkAt_congr rfl rfl hbk, hst⟩

/-- **INV-1, INV-5, INV-6, INV-7, INV-8, INV-13, INV-14 for `process`.** -/
theorem process_preserves_FullBookInv (b : BookState) (o : Order)
    (hb : BookOk b) (hstops : StopsWF b) (hok : OrderRestOk o) :
    FullBookInv (process b o).book :=
  FullBookInv_of_BookOkAt (process_preserves_BookOk b o hb hstops hok).1

/-- **INV-11 and INV-12 for `process`**, unconditionally. -/
theorem process_emits_safe_trades (b : BookState) (o : Order) :
    TradesOk (process b o).trades :=
  (process_all_TradesOk defaultFuel).1 _ _

/-- INV-11 in the form stated in `Invariants.lean`. -/
theorem process_PostOnlyGuarantee (b : BookState) (o : Order) :
    PostOnlyGuarantee (process b o).trades :=
  fun t ht => (process_emits_safe_trades b o t ht).1

/-- INV-12 in the form stated in `Invariants.lean`. -/
theorem process_STPGuarantee (b : BookState) (o : Order) :
    STPGuarantee (process b o).trades :=
  fun t ht => (process_emits_safe_trades b o t ht).2

-- ============================================================================
-- The preconditions are discharged by well-formedness and by the empty book
-- ============================================================================

/-- `OrderRestOk` asks for nothing beyond `Order.WellFormed`: clause one is
    WF-1 with WF-11, clause two is WF-13. -/
theorem OrderRestOk_of_WellFormed {o : Order} (h : o.WellFormed) : OrderRestOk o := by
  unfold Order.WellFormed at h
  obtain ⟨hq, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpo, -, -, -, -, -, -, -, hrq⟩ := h
  exact ⟨by rw [hrq]; exact hq, hpo⟩

theorem BookOk_empty : BookOk BookState.empty := by
  constructor <;> (intro l hl; cases hl)

theorem StopsWF_empty : StopsWF BookState.empty := by
  intro s hs; cases hs

-- ============================================================================
-- Capstone: the full §13 book-state suite for `process`
-- ============================================================================

/-- **`BookInvariant` (the full §13 book-state suite) is preserved by `process`.**

    This combines the `AllInv` half proved in `Theorems.lean` (INV-2/3 sorting
    and `BookUncrossed`) with the seven invariants proved here. Together with
    `process_PostOnlyGuarantee` and `process_STPGuarantee` — which need no
    hypotheses at all — this covers every invariant in §13. -/
theorem process_preserves_BookInvariant (b : BookState) (o : Order)
    (hall : AllInv b) (hpok : OrderProcOk o) (hsnp : StopsNoPostOnly b)
    (hb : BookOk b) (hstops : StopsWF b) (hok : OrderRestOk o) :
    BookInvariant (process b o).book := by
  obtain ⟨hne, hng, hsc, hfifo, hnm, hnmtl, hnmq⟩ :=
    process_preserves_FullBookInv b o hb hstops hok
  exact ⟨process_preserves_uncrossed b o hpok hsnp hall, hng, hsc, hnm, hnmtl, hnmq, hne, hfifo⟩
