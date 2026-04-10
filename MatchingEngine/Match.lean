import MatchingEngine.Book
import MatchingEngine.STP

/-!
# Matching Engine — Core Matching Loop (§5.1)

Implements DoMatch with fuel-bounded recursion.
Includes STP handling, iceberg reload, and the BUG-1/BUG-2 fixes.
-/

-- §5.1 Step 2: Price compatibility predicate
def canMatchPrice (inc : Order) (restingPrice : Price) : Bool :=
  match inc.price with
  | none   => true   -- MARKET: matches any price
  | some p =>
    match inc.side with
    | .buy  => p >= restingPrice
    | .sell => p <= restingPrice

-- Result of the matching loop
structure MatchResult where
  incoming : Order
  bids     : List PriceLevel
  asks     : List PriceLevel
  trades   : List Trade
  clock    : Timestamp
  deriving Repr

/-- Core matching loop (§5.1 Step 3).
    Fuel-bounded mutual recursion. Each call processes one resting order interaction.

    INCLUDES:
    - STP handling with all four policies (§8.3)
    - BUG-2 FIX: iceberg reload after STP DECREMENT
    - Iceberg reload after normal fill (§7.5)
    - Skipping zero-visible orders
-/
def doMatch (fuel : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp) : MatchResult :=
  match fuel with
  | 0 => { incoming := inc, bids := bids, asks := asks, trades := trades, clock := tm }
  | fuel' + 1 =>
    if inc.remainingQty == 0 || inc.status == .cancelled then
      { incoming := inc, bids := bids, asks := asks, trades := trades, clock := tm }
    else
      -- Determine contra side
      let contraLevels := match inc.side with | .buy => asks | .sell => bids
      match contraLevels with
      | [] =>
        { incoming := inc, bids := bids, asks := asks, trades := trades, clock := tm }
      | level :: restLevels =>
        if !canMatchPrice inc level.price then
          { incoming := inc, bids := bids, asks := asks, trades := trades, clock := tm }
        else
          match level.orders with
          | [] =>
            -- Empty level, skip (shouldn't happen with INV-1/2, but defensive)
            let setContra := fun lvls => match inc.side with
              | .buy  => (bids, lvls)
              | .sell => (lvls, asks)
            let (bids', asks') := setContra restLevels
            doMatch fuel' inc bids' asks' trades tm
          | resting :: restOrders =>
            -- Skip zero-visible non-conflicting orders
            if resting.visibleQty == 0 && !selfTradeConflict inc resting then
              -- Remove from queue (spec gap: stranded order)
              let level' := if restOrders.isEmpty then restLevels
                           else { level with orders := restOrders } :: restLevels
              let setContra := fun lvls => match inc.side with
                | .buy  => (bids, lvls)
                | .sell => (lvls, asks)
              let (bids', asks') := setContra level'
              doMatch fuel' inc bids' asks' trades tm
            else if selfTradeConflict inc resting then
              -- §8.3 STP handling
              let policy := inc.stpPolicy.getD .cancelNewest
              match policy with
              | .cancelNewest =>
                let inc' := { inc with status := .cancelled }
                { incoming := inc', bids := bids, asks := asks, trades := trades, clock := tm }
              | .cancelOldest =>
                let level' := if restOrders.isEmpty then restLevels
                             else { level with orders := restOrders } :: restLevels
                let setContra := fun lvls => match inc.side with
                  | .buy  => (bids, lvls)
                  | .sell => (lvls, asks)
                let (bids', asks') := setContra level'
                doMatch fuel' inc bids' asks' trades tm
              | .cancelBoth =>
                let inc' := { inc with status := .cancelled }
                let level' := if restOrders.isEmpty then restLevels
                             else { level with orders := restOrders } :: restLevels
                let setContra := fun lvls => match inc.side with
                  | .buy  => (bids, lvls)
                  | .sell => (lvls, asks)
                let (bids', asks') := setContra level'
                { incoming := inc', bids := bids', asks := asks', trades := trades, clock := tm }
              | .decrement =>
                let reduceQty := min inc.remainingQty resting.visibleQty
                if reduceQty == 0 then
                  -- Can't decrement; remove stranded order
                  let level' := if restOrders.isEmpty then restLevels
                               else { level with orders := restOrders } :: restLevels
                  let setContra := fun lvls => match inc.side with
                    | .buy  => (bids, lvls)
                    | .sell => (lvls, asks)
                  let (bids', asks') := setContra level'
                  doMatch fuel' inc bids' asks' trades tm
                else
                  let incRem := inc.remainingQty - reduceQty
                  let restRem := resting.remainingQty - reduceQty
                  let restVis := resting.visibleQty - reduceQty
                  let inc' := { inc with
                    remainingQty := incRem,
                    status := if incRem == 0 then .cancelled else inc.status }
                  let rest' := { resting with
                    remainingQty := restRem,
                    visibleQty := restVis }
                  if restRem == 0 then
                    let level' := if restOrders.isEmpty then restLevels
                                 else { level with orders := restOrders } :: restLevels
                    let setContra := fun lvls => match inc.side with
                      | .buy  => (bids, lvls)
                      | .sell => (lvls, asks)
                    let (bids', asks') := setContra level'
                    doMatch fuel' inc' bids' asks' trades tm
                  else if restVis == 0 && rest'.displayQty.isSome then
                    -- BUG-2 FIX: Reload iceberg after DECREMENT
                    let reloadQty := min (rest'.displayQty.getD 0) restRem
                    let reloaded := { rest' with
                      visibleQty := reloadQty,
                      timestamp := tm,
                      status := .partiallyFilled }
                    let level' := if restOrders.isEmpty then
                                    [{ level with orders := [reloaded] }]
                                  else
                                    { level with orders := restOrders ++ [reloaded] } :: []
                    -- Rebuild: keep rest of levels
                    let allLevels := level' ++ restLevels.drop 0  -- all remaining after current
                    -- Actually need to reconstruct properly
                    let newQueue := restOrders ++ [reloaded]
                    let level'' := if newQueue.isEmpty then restLevels
                                  else { level with orders := newQueue } :: restLevels
                    let setContra := fun lvls => match inc.side with
                      | .buy  => (bids, lvls)
                      | .sell => (lvls, asks)
                    let (bids', asks') := setContra level''
                    doMatch fuel' inc' bids' asks' trades (tm + 1)
                  else
                    let newQueue := rest' :: restOrders
                    let level' := { level with orders := newQueue } :: restLevels
                    let setContra := fun lvls => match inc.side with
                      | .buy  => (bids, lvls)
                      | .sell => (lvls, asks)
                    let (bids', asks') := setContra level'
                    doMatch fuel' inc' bids' asks' trades tm
            else
              -- Normal fill
              let fillQty := min inc.remainingQty resting.visibleQty
              let inc' := { inc with remainingQty := inc.remainingQty - fillQty }
              let rest' := { resting with
                visibleQty := resting.visibleQty - fillQty,
                remainingQty := resting.remainingQty - fillQty }
              let trade : Trade := {
                price := level.price,
                qty := fillQty,
                aggressorId := inc.id,
                passiveId := resting.id,
                aggressorSide := inc.side,
                aggPostOnly := inc.postOnly,
                aggStpGroup := inc.stpGroup,
                pasStpGroup := resting.stpGroup }
              let trades' := trades ++ [trade]

              if rest'.remainingQty == 0 then
                -- Fully filled, remove
                let level' := if restOrders.isEmpty then restLevels
                             else { level with orders := restOrders } :: restLevels
                let setContra := fun lvls => match inc.side with
                  | .buy  => (bids, lvls)
                  | .sell => (lvls, asks)
                let (bids', asks') := setContra level'
                doMatch fuel' inc' bids' asks' trades' tm
              else if rest'.visibleQty == 0 && rest'.displayQty.isSome then
                -- Iceberg reload (§7.5)
                let reloadQty := min (rest'.displayQty.getD 0) rest'.remainingQty
                let reloaded := { rest' with
                  visibleQty := reloadQty,
                  timestamp := tm,
                  status := .partiallyFilled }
                -- Move to back of queue
                let newQueue := restOrders ++ [reloaded]
                let level' := { level with orders := newQueue } :: restLevels
                let setContra := fun lvls => match inc.side with
                  | .buy  => (bids, lvls)
                  | .sell => (lvls, asks)
                let (bids', asks') := setContra level'
                doMatch fuel' inc' bids' asks' trades' (tm + 1)
              else
                -- Partial fill
                let updRest := { rest' with status := .partiallyFilled }
                let newQueue := updRest :: restOrders
                let level' := { level with orders := newQueue } :: restLevels
                let setContra := fun lvls => match inc.side with
                  | .buy  => (bids, lvls)
                  | .sell => (lvls, asks)
                let (bids', asks') := setContra level'
                doMatch fuel' inc' bids' asks' trades' tm

-- Convenience wrapper that extracts contra/same from BookState
def matchOrder (fuel : Nat) (b : BookState) (inc : Order) : MatchResult :=
  let result := doMatch fuel inc b.bids b.asks [] (b.clock + 1)
  result
