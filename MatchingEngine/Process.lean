import MatchingEngine.Match

/-!
# Matching Engine — Processing Pipeline (§12)

Full PROCESS pipeline including stop handling, post-only, FOK/MinQty,
MTL routing, matching, disposition, and stop cascade.
Includes BUG-1 FIX: timestamp refresh on stop trigger.
-/

-- Default fuel for the mutual processing recursion (stop cascade depth).
-- NOTE: This fuel bounds only the stop cascade depth, not matching itself.
-- Matching fuel is computed from the book state via `computeMatchFuel` and
-- is proven sufficient — see `doMatch_terminates_with_computed_fuel`.
def defaultFuel : Nat := 100

/-- Computed fuel for doMatch, derived from the contra side.

    Measure: `Σ remainingQty + orderCount + levelCount + 1`.

    This is a conservative upper bound on the number of steps doMatch
    needs to complete matching. Each step strictly decreases at least
    one component:
    - Fill steps decrease sum of contra remainingQty (by ≥ 1)
    - STP skip / zero-visible skip / full removal decrease orderCount
    - Empty-level skip decreases levelCount
    - Iceberg reload is part of a fill step (sum already decreased)

    Therefore fuel = measure is sufficient for doMatch to reach a
    terminal state (no more matchable orders or inc exhausted). -/
def computeMatchFuel (b : BookState) (side : Side) : Nat :=
  let contra := contraLevels b side
  let sumQty := contra.foldl (fun acc lvl =>
    acc + lvl.orders.foldl (fun a o => a + o.remainingQty) 0) 0
  let orderCount := contra.foldl (fun acc lvl => acc + lvl.orders.length) 0
  let levelCount := contra.length
  sumQty + orderCount + levelCount + 1

-- §5.3 FOK pre-check: sum available non-conflicting visible qty
def availableQty (inc : Order) (levels : List PriceLevel) : Nat :=
  levels.foldl (fun acc level =>
    if !canMatchPrice inc level.price then acc
    else acc + level.orders.foldl (fun a r =>
      if selfTradeConflict inc r then a else a + r.visibleQty) 0
  ) 0

def fokCheck (inc : Order) (b : BookState) : Bool :=
  let contra := contraLevels b inc.side
  availableQty inc contra >= inc.qty

-- §5.4 MinQty pre-check
def minQtyCheck (inc : Order) (b : BookState) : Bool :=
  match inc.minQty with
  | none => true
  | some mq =>
    let contra := contraLevels b inc.side
    availableQty inc contra >= mq

-- §7.6 Post-only crossing check (REJECT policy)
def wouldCross (inc : Order) (b : BookState) : Bool :=
  match inc.price with
  | none => false
  | some p =>
    match inc.side with
    | .buy =>
      match bestAskPrice b with
      | none => false
      | some askP => p >= askP
    | .sell =>
      match bestBidPrice b with
      | none => false
      | some bidP => p <= bidP

-- §5.2 Post-match disposition
def dispose (inc : Order) (b : BookState) (trades : List Trade) : BookState :=
  if inc.remainingQty == 0 || inc.status == .cancelled then b
  else if inc.tif == .ioc then b  -- IOC: cancel remainder
  else if inc.orderType == .market then b  -- Markets never rest
  else insertOrder b inc (!trades.isEmpty)  -- GTC/DAY: rest on book

-- §10 Stop order helpers

/-- Check if stop should trigger (§10.1) -/
def shouldTrigger (stop : Order) (lastTP : Option Price) : Bool :=
  match lastTP, stop.stopPrice with
  | some tp, some sp =>
    match stop.side with
    | .buy  => tp >= sp
    | .sell => tp <= sp
  | _, _ => false

/-- Convert stop to base type (§10.1).
    BUG-1 FIX: assigns fresh timestamp. -/
def convertStop (stop : Order) (newTimestamp : Timestamp) : Order :=
  match stop.orderType with
  | .stopLimit =>
    { stop with orderType := .limit, stopPrice := none,
                status := .new_, timestamp := newTimestamp }
  | .stopMarket =>
    { stop with orderType := .market, stopPrice := none,
                price := none, status := .new_, timestamp := newTimestamp }
  | _ => stop

-- Result of processing
structure ProcessResult where
  book   : BookState
  trades : List Trade
  deriving Repr, Inhabited

-- Mutually recursive processing functions
mutual

/-- Process a single order through the full pipeline (§12). -/
def processOrder (fuel : Nat) (order : Order) (b : BookState) : ProcessResult :=
  match fuel with
  | 0 => { book := b, trades := [] }
  | fuel' + 1 =>
    -- Phase 1: Stop order handling
    if order.orderType == .stopLimit || order.orderType == .stopMarket then
      if shouldTrigger order b.lastTradePrice then
        let converted := convertStop order b.clock
        let b' := { b with clock := b.clock + 1 }
        processOrder fuel' converted b'
      else
        { book := { b with stops := b.stops ++ [order] }, trades := [] }
    -- Phase 2: Post-only check (REJECT policy)
    else if order.postOnly then
      if wouldCross order b then
        { book := b, trades := [] }
      else
        { book := insertOrder b order false, trades := [] }
    -- Phase 3: FOK pre-check
    else if order.tif == .fok then
      if !fokCheck order b then
        { book := b, trades := [] }
      else
        let mr := matchOrder (computeMatchFuel b order.side) b order
        let b' := { b with bids := mr.bids, asks := mr.asks, clock := mr.clock }
        let newLTP := mr.trades.getLast?.map (·.price)
        let b'' := { b' with lastTradePrice := newLTP.orElse (fun _ => b.lastTradePrice) }
        let cascade := processCascade fuel' mr.trades b''
        { book := cascade.book, trades := mr.trades ++ cascade.trades }
    -- Phase 3b: MinQty pre-check
    else if order.minQty.isSome then
      if !minQtyCheck order b then
        { book := b, trades := [] }
      else
        let mr := matchOrder (computeMatchFuel b order.side) b order
        let inc := if !mr.trades.isEmpty then
          { mr.incoming with minQty := none }
        else mr.incoming
        let b' := { b with bids := mr.bids, asks := mr.asks, clock := mr.clock }
        let b'' := dispose inc b' mr.trades
        let newLTP := mr.trades.getLast?.map (·.price)
        let b''' := { b'' with lastTradePrice := newLTP.orElse (fun _ => b.lastTradePrice) }
        let cascade := processCascade fuel' mr.trades b'''
        { book := cascade.book, trades := mr.trades ++ cascade.trades }
    -- Phase 4: MTL routing
    else if order.orderType == .marketToLimit then
      let mr := matchOrder (computeMatchFuel b order.side) b order
      if mr.trades.isEmpty then
        { book := { b with bids := mr.bids, asks := mr.asks, clock := mr.clock }, trades := [] }
      else
        let limitPrice := mr.trades.head!.price
        let converted := { mr.incoming with
          orderType := .limit, price := some limitPrice, minQty := none }
        let b' := { b with bids := mr.bids, asks := mr.asks, clock := mr.clock }
        if converted.remainingQty == 0 then
          let newLTP := mr.trades.getLast?.map (·.price)
          let b'' := { b' with lastTradePrice := newLTP.orElse (fun _ => b.lastTradePrice) }
          let cascade := processCascade fuel' mr.trades b''
          { book := cascade.book, trades := mr.trades ++ cascade.trades }
        else
          let mr2 := doMatch (computeMatchFuel b' converted.side) converted b'.bids b'.asks [] mr.clock
          let allTrades := mr.trades ++ mr2.trades
          let b'' := { b' with bids := mr2.bids, asks := mr2.asks, clock := mr2.clock }
          let b''' := dispose mr2.incoming b'' allTrades
          let newLTP := allTrades.getLast?.map (·.price)
          let b4 := { b''' with lastTradePrice := newLTP.orElse (fun _ => b.lastTradePrice) }
          let cascade := processCascade fuel' allTrades b4
          { book := cascade.book, trades := allTrades ++ cascade.trades }
    -- Phase 5: Normal matching
    else
      let mr := matchOrder (computeMatchFuel b order.side) b order
      let inc := if order.minQty.isSome && !mr.trades.isEmpty then
        { mr.incoming with minQty := none }
      else mr.incoming
      let b' := { b with bids := mr.bids, asks := mr.asks, clock := mr.clock }
      let b'' := dispose inc b' mr.trades
      let newLTP := mr.trades.getLast?.map (·.price)
      let b''' := { b'' with lastTradePrice := newLTP.orElse (fun _ => b.lastTradePrice) }
      let cascade := processCascade fuel' mr.trades b'''
      { book := cascade.book, trades := mr.trades ++ cascade.trades }

/-- Process stop cascade: evaluate stops after each trade (§10.1, §10.2). -/
def processCascade (fuel : Nat) (trades : List Trade) (b : BookState) : ProcessResult :=
  match fuel, trades with
  | 0, _ => { book := b, trades := [] }
  | _, [] => { book := b, trades := [] }
  | fuel' + 1, t :: rest =>
    let tp := t.price
    let (triggered, remaining) := b.stops.partition (fun s => shouldTrigger s (some tp))
    if triggered.isEmpty then
      processCascade fuel' rest { b with lastTradePrice := some tp }
    else
      let sorted := triggered.mergeSort (fun a c => a.timestamp < c.timestamp)
      let b' := { b with stops := remaining, lastTradePrice := some tp }
      let result := processTriggeredStops fuel' sorted b'
      let cascade2 := processCascade fuel' rest result.book
      { book := cascade2.book, trades := result.trades ++ cascade2.trades }

/-- Process each triggered stop in timestamp order. -/
def processTriggeredStops (fuel : Nat) (triggered : List Order)
    (b : BookState) : ProcessResult :=
  match fuel, triggered with
  | 0, _ => { book := b, trades := [] }
  | _, [] => { book := b, trades := [] }
  | fuel' + 1, stop :: rest =>
    let converted := convertStop stop b.clock
    let b' := { b with clock := b.clock + 1 }
    let result := processOrder fuel' converted b'
    let rest' := processTriggeredStops fuel' rest result.book
    { book := rest'.book, trades := result.trades ++ rest'.trades }

end

/-- Top-level process: creates order with next ID and timestamp. -/
def process (b : BookState) (order : Order) : ProcessResult :=
  let o := { order with id := b.nextId, timestamp := b.clock }
  let result := processOrder defaultFuel o b
  let newClock := Nat.max (result.book.clock) (b.clock + 1)
  let b' := { result.book with nextId := b.nextId + 1, clock := newClock }
  { book := b', trades := result.trades }
