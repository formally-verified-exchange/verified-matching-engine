import MatchingEngine

/-! Enumerate exactly the shape space `SubmitOrder` quantifies over in
    MatchingEngine.tla and emit the ones Lean's `Order.wellFormed` accepts,
    in the canonical form used by the TLA emitter. Tuple field order:
    side, type, tif, price, stopPrice, qty, displayQty, postOnly, minQty,
    stpGroup, stpPolicy. -/

def sideS : Side → String | .buy => "BUY" | .sell => "SELL"
def typeS : OrderType → String
  | .limit => "LIMIT" | .market => "MARKET" | .marketToLimit => "MTL"
  | .stopLimit => "STOP_LIMIT" | .stopMarket => "STOP_MARKET"
def tifS : TimeInForce → String
  | .gtc => "GTC" | .ioc => "IOC" | .fok => "FOK" | .day => "DAY"
def polS : STPPolicy → String
  | .cancelNewest => "CANCEL_NEWEST" | .cancelOldest => "CANCEL_OLDEST"
  | .cancelBoth => "CANCEL_BOTH" | .decrement => "DECREMENT"
def optN (o : Option Nat) : String := match o with | some n => toString n | none => "NULL"

def PRICESL : List (Option Price) := [some 1, some 2, some 3, none]
def OPTQ    : List (Option Nat)   := [some 1, some 2, none]

def shapes : List String :=
  [Side.buy, Side.sell].flatMap fun sd =>
  [OrderType.limit, .market, .marketToLimit, .stopLimit, .stopMarket].flatMap fun ot =>
  [TimeInForce.gtc, .ioc, .fok, .day].flatMap fun tf =>
  PRICESL.flatMap fun pr =>
  PRICESL.flatMap fun sp =>
  [1, 2].flatMap fun qt =>
  OPTQ.flatMap fun dq =>
  [false, true].flatMap fun po =>
  OPTQ.flatMap fun mq =>
  [(none : Option StpGroup), some 1].flatMap fun sg =>
  [(none : Option STPPolicy), some .cancelNewest, some .cancelOldest,
   some .cancelBoth, some .decrement].flatMap fun sl =>
    let o : Order :=
      { id := 1, side := sd, orderType := ot, tif := tf,
        price := pr, stopPrice := sp, qty := qt, remainingQty := qt,
        minQty := mq, displayQty := dq,
        visibleQty := match dq with | some d => min d qt | none => qt,
        postOnly := po, status := .new_, timestamp := 0,
        stpGroup := sg, stpPolicy := sl }
    if o.wellFormed then
      [String.intercalate "|"
        [sideS sd, typeS ot, tifS tf, optN pr, optN sp, toString qt,
         optN dq, (if po then "TRUE" else "FALSE"), optN mq,
         (match sg with | some _ => "G1" | none => "NULL"),
         (match sl with | some p => polS p | none => "NULL")]]
    else []

def main : IO Unit := do
  IO.println s!"COUNT {shapes.length}"
  for l in shapes.toArray.qsort (· < ·) do IO.println l
