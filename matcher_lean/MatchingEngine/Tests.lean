import MatchingEngine.Process
import MatchingEngine.Invariants
import MatchingEngine.Cancel
-- IMPORTANT: import Theorems so the default build target type-checks it.
-- (Without this, Theorems.lean silently escapes the build.)
import MatchingEngine.Theorems

/-!
# Matching Engine — Comprehensive Test Suite
-/

open Side OrderType TimeInForce OrderStatus STPPolicy

-- ============================================================================
-- Order constructors
-- ============================================================================

def mkLimit (s : Side) (p : Price) (q : Quantity) (tif : TimeInForce := .gtc) : Order :=
  { id := 0, side := s, orderType := .limit, tif := tif,
    price := some p, stopPrice := none, qty := q, remainingQty := q,
    minQty := none, displayQty := none, visibleQty := q,
    postOnly := false, status := .new_, timestamp := 0,
    stpGroup := none, stpPolicy := none }

def mkMarket (s : Side) (q : Quantity) (tif : TimeInForce := .ioc) : Order :=
  { id := 0, side := s, orderType := .market, tif := tif,
    price := none, stopPrice := none, qty := q, remainingQty := q,
    minQty := none, displayQty := none, visibleQty := q,
    postOnly := false, status := .new_, timestamp := 0,
    stpGroup := none, stpPolicy := none }

def mkStopLimit (s : Side) (p sp : Price) (q : Quantity) : Order :=
  { id := 0, side := s, orderType := .stopLimit, tif := .gtc,
    price := some p, stopPrice := some sp, qty := q, remainingQty := q,
    minQty := none, displayQty := none, visibleQty := q,
    postOnly := false, status := .new_, timestamp := 0,
    stpGroup := none, stpPolicy := none }

def mkIceberg (s : Side) (p : Price) (q : Quantity) (dq : Quantity) : Order :=
  { id := 0, side := s, orderType := .limit, tif := .gtc,
    price := some p, stopPrice := none, qty := q, remainingQty := q,
    minQty := none, displayQty := some dq, visibleQty := min dq q,
    postOnly := false, status := .new_, timestamp := 0,
    stpGroup := none, stpPolicy := none }

def mkPostOnly (s : Side) (p : Price) (q : Quantity) : Order :=
  { id := 0, side := s, orderType := .limit, tif := .gtc,
    price := some p, stopPrice := none, qty := q, remainingQty := q,
    minQty := none, displayQty := none, visibleQty := q,
    postOnly := true, status := .new_, timestamp := 0,
    stpGroup := none, stpPolicy := none }

def mkMTL (s : Side) (q : Quantity) : Order :=
  { id := 0, side := s, orderType := .marketToLimit, tif := .gtc,
    price := none, stopPrice := none, qty := q, remainingQty := q,
    minQty := none, displayQty := none, visibleQty := q,
    postOnly := false, status := .new_, timestamp := 0,
    stpGroup := none, stpPolicy := none }

def mkWithSTP (o : Order) (grp : StpGroup) (pol : STPPolicy) : Order :=
  { o with stpGroup := some grp, stpPolicy := some pol }

def mkWithMinQty (o : Order) (mq : Quantity) : Order :=
  { o with minQty := some mq }

-- ============================================================================
-- Helper
-- ============================================================================

def runOrders (orders : List Order) : BookState × List Trade :=
  orders.foldl (fun (b, ts) o =>
    let r := process b o
    (r.book, ts ++ r.trades)
  ) (BookState.empty, [])

-- ============================================================================
-- Tests
-- ============================================================================

def test_appendixB : IO Unit := do
  let s1 := process BookState.empty (mkLimit .buy 1005 100)
  assert! s1.book.bids.length == 1
  assert! s1.trades.isEmpty

  let s2 := process s1.book (mkLimit .buy 1005 50)
  assert! s2.book.bids.length == 1
  assert! (s2.book.bids.head?.map (·.orders.length)).getD 0 == 2

  let s3 := process s2.book (mkLimit .buy 1010 75)
  assert! s3.book.bids.length == 2

  let s4 := process s3.book (mkLimit .sell 995 30)
  assert! s4.trades.length == 1
  assert! (s4.trades.head?.map (·.qty)).getD 0 == 30
  assert! (s4.trades.head?.map (·.price)).getD 0 == 1010

  let s5 := process s4.book (mkMarket .sell 200)
  assert! s5.trades.length == 3
  assert! s5.trades.foldl (fun a t => a + t.qty) 0 == 195
  assert! s5.book.bids.isEmpty && s5.book.asks.isEmpty

  IO.println "✓ Test 1: Appendix B walkthrough"

def test_bug1 : IO Unit := do
  let s1 := process BookState.empty (mkLimit .sell 1 1)
  let s2 := process s1.book (mkStopLimit .buy 1 1 1)
  assert! s2.book.stops.length == 1
  let s3 := process s2.book (mkLimit .buy 1 2)
  assert! s3.trades.length == 1
  assert! fifoWithinLevelB s3.book
  assert! bookInvariantB s3.book
  match s3.book.bids.head? with
  | some level =>
    match level.orders with
    | o1 :: o2 :: _ => assert! o1.timestamp < o2.timestamp
    | _ => pure ()
  | _ => pure ()
  IO.println "✓ Test 2: BUG-1 FIFO fix"

def test_bug2 : IO Unit := do
  let icebergAsk : Order :=
    { id := 1, side := .sell, orderType := .limit, tif := .gtc,
      price := some 100, stopPrice := none, qty := 2, remainingQty := 2,
      minQty := none, displayQty := some 1, visibleQty := 1,
      postOnly := false, status := .new_, timestamp := 1,
      stpGroup := some 1, stpPolicy := some .decrement }
  let book : BookState :=
    { bids := [], asks := [{ price := 100, orders := [icebergAsk] }],
      stops := [], lastTradePrice := none, nextId := 2, clock := 2 }
  let r := process book (mkWithSTP (mkLimit .buy 100 1 .ioc) 1 .decrement)
  assert! r.trades.isEmpty
  assert! r.book.asks.length == 1
  match r.book.asks.head?.bind (·.orders.head?) with
  | some o =>
    assert! o.visibleQty > 0
    assert! o.remainingQty == 1
  | none => assert! false
  IO.println "✓ Test 3: BUG-2 iceberg DECREMENT reload"

def test_fok : IO Unit := do
  let s1 := process BookState.empty (mkLimit .sell 100 5)
  let s2 := process s1.book (mkLimit .buy 100 10 .fok)
  assert! s2.trades.isEmpty
  assert! s2.book.asks.length == 1
  let s3 := process s1.book (mkLimit .buy 100 3 .fok)
  assert! s3.trades.length == 1
  assert! (s3.trades.head?.map (·.qty)).getD 0 == 3
  IO.println "✓ Test 4: FOK reject/accept"

def test_ioc : IO Unit := do
  let s1 := process BookState.empty (mkLimit .sell 100 3)
  let s2 := process s1.book (mkLimit .buy 100 5 .ioc)
  assert! s2.trades.length == 1
  assert! (s2.trades.head?.map (·.qty)).getD 0 == 3
  assert! s2.book.bids.isEmpty
  IO.println "✓ Test 5: IOC partial fill + cancel"

def test_marketSweep : IO Unit := do
  let (b, _) := runOrders [
    mkLimit .sell 101 10,
    mkLimit .sell 102 20,
    mkLimit .sell 103 30
  ]
  assert! b.asks.length == 3
  let r := process b (mkMarket .buy 25)
  assert! r.trades.length == 2
  assert! r.trades.foldl (fun a t => a + t.qty) 0 == 25
  IO.println "✓ Test 6: MARKET sweep"

def test_mtl : IO Unit := do
  let s1 := process BookState.empty (mkLimit .sell 100 3)
  let s2 := process s1.book (mkMTL .buy 5)
  assert! s2.trades.length == 1
  assert! (s2.trades.head?.map (·.qty)).getD 0 == 3
  assert! s2.book.bids.length == 1
  assert! (bestBidPrice s2.book).getD 0 == 100
  assert! noRestingMarketsB s2.book
  assert! noRestingMtlB s2.book
  IO.println "✓ Test 7: MTL fill-convert-rest"

def test_postOnly : IO Unit := do
  let s1 := process BookState.empty (mkLimit .sell 100 5)
  let s2 := process s1.book (mkPostOnly .buy 100 3)
  assert! s2.trades.isEmpty
  assert! s2.book.bids.isEmpty
  let s3 := process s1.book (mkPostOnly .buy 99 3)
  assert! s3.trades.isEmpty
  assert! s3.book.bids.length == 1
  IO.println "✓ Test 8: Post-only reject/accept"

def test_minQty : IO Unit := do
  let s1 := process BookState.empty (mkLimit .sell 100 5)
  let s2 := process s1.book (mkWithMinQty (mkLimit .buy 100 15) 10)
  assert! s2.trades.isEmpty
  let s3 := process s1.book (mkWithMinQty (mkLimit .buy 100 15) 3)
  assert! s3.trades.length == 1
  assert! noRestingMinQtyB s3.book
  IO.println "✓ Test 9: MinQty reject/accept/clear"

def test_iceberg : IO Unit := do
  let s1 := process BookState.empty (mkIceberg .sell 100 6 2)
  match s1.book.asks.head?.bind (·.orders.head?) with
  | some o => assert! o.visibleQty == 2
  | none => assert! false
  let s2 := process s1.book (mkLimit .buy 100 2)
  assert! s2.trades.length == 1
  assert! (s2.trades.head?.map (·.qty)).getD 0 == 2
  match s2.book.asks.head?.bind (·.orders.head?) with
  | some o =>
    assert! o.remainingQty == 4
    assert! o.visibleQty == 2
  | none => assert! false
  IO.println "✓ Test 10: Iceberg fill-reload"

def test_stp : IO Unit := do
  let s1 := process BookState.empty (mkWithSTP (mkLimit .sell 100 5) 1 .cancelNewest)
  let s2 := process s1.book (mkWithSTP (mkLimit .buy 100 3) 1 .cancelNewest)
  assert! s2.trades.isEmpty
  assert! s2.book.asks.length == 1

  let s3 := process BookState.empty (mkWithSTP (mkLimit .sell 100 5) 1 .cancelOldest)
  let s4 := process s3.book (mkWithSTP (mkLimit .buy 100 3) 1 .cancelOldest)
  assert! s4.trades.isEmpty
  assert! s4.book.asks.isEmpty

  let s5 := process BookState.empty (mkWithSTP (mkLimit .sell 100 5) 1 .cancelBoth)
  let s6 := process s5.book (mkWithSTP (mkLimit .buy 100 3) 1 .cancelBoth)
  assert! s6.trades.isEmpty
  assert! s6.book.asks.isEmpty && s6.book.bids.isEmpty

  IO.println "✓ Test 11: STP policies"

def test_cancel : IO Unit := do
  let s1 := process BookState.empty (mkLimit .buy 100 5)
  match cancelOrder s1.book 1 with
  | some b =>
    assert! b.bids.isEmpty
    assert! bookInvariantB b
  | none => assert! false
  IO.println "✓ Test 12: Cancel"

def test_amendQtyDecrease : IO Unit := do
  let (b, _) := runOrders [mkLimit .buy 100 10, mkLimit .buy 100 5]
  match amendQtyDecrease b 1 3 with
  | some b' =>
    match b'.bids.head?.bind (·.orders.head?) with
    | some o => assert! o.id == 1 && o.remainingQty == 3
    | none => assert! false
    assert! fifoWithinLevelB b'
  | none => assert! false
  IO.println "✓ Test 13: Amend qty decrease"

def test_stopCascade : IO Unit := do
  let s1 := process BookState.empty (mkLimit .sell 10 1)
  let s2 := process s1.book (mkStopLimit .buy 10 10 1)
  let s3 := process s2.book (mkStopLimit .buy 10 10 1)
  assert! s3.book.stops.length == 2
  let s4 := process s3.book (mkLimit .buy 10 1)
  assert! s4.trades.length >= 1
  assert! s4.book.stops.isEmpty
  assert! bookInvariantB s4.book
  IO.println "✓ Test 14: Stop cascade"

def test_complexSequence : IO Unit := do
  let orders := [
    mkLimit .buy 100 10,
    mkLimit .buy 101 5,
    mkLimit .sell 105 8,
    mkLimit .sell 103 3,
    mkLimit .buy 103 2,
    mkLimit .sell 100 20,
    mkLimit .buy 102 4 .ioc,
    mkPostOnly .buy 102 5,
  ]
  let (b, _) := runOrders orders
  assert! bookInvariantB b
  assert! bookUncrossedB b
  IO.println "✓ Test 15: Complex sequence invariants"

def test_emptyBookInvariants : IO Unit := do
  assert! bookInvariantB BookState.empty
  IO.println "✓ Test 16: Empty book invariants"

def runAllTests : IO Unit := do
  test_emptyBookInvariants
  test_appendixB
  test_bug1
  test_bug2
  test_fok
  test_ioc
  test_marketSweep
  test_mtl
  test_postOnly
  test_minQty
  test_iceberg
  test_stp
  test_cancel
  test_amendQtyDecrease
  test_stopCascade
  test_complexSequence
  IO.println "\nAll 16 tests passed!"
