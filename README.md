# Verified Matching Engine

A feature-rich price-time priority matching engine verified at two
levels: bounded exhaustive state-space exploration with TLA+/TLC, and
a mechanized proof in Lean 4 that the processing pipeline preserves
the combined book invariant `BookInvariant` (uncrossed, no ghost
orders, status consistency, no resting marketable/MTL/MinQty orders,
no empty levels, and FIFO ordering within a level), plus unconditional
post-only and self-trade-prevention guarantees on emitted trades.

The full write-up is in `paper.tex` / `paper.pdf`. This README
describes how to build and run the two verification artifacts.

## Repository layout

```
matching-engine-formal-spec.md   Prose specification (v1.2.0, 979 lines)
matcher_tla/                     TLA+ specification and TLC configs
  MatchingEngine.tla             TLA+ model (~950 lines)
  MatchingEngine.cfg             TLC config: 2 orders / 3 prices (medium)
  MatchingEngine_noamend.cfg     TLC config: 3 orders / 2 prices
  MatchingEngine_amend.cfg       TLC config: with AmendOrder action
  REPORT.md                      Model checking findings and bug traces
matcher_lean/                    Self-contained Lean 4 project
  lakefile.toml                  Lake build configuration
  lean-toolchain                 Pinned Lean toolchain
  Main.lean                      Executable entry point (runs Tests)
  MatchingEngine.lean            Library root (imports every module)
  MatchingEngine/                Lean 4 sources
    Basic.lean, Order.lean, Book.lean, STP.lean,
    Match.lean, Process.lean, Cancel.lean, Invariants.lean,
    Tests.lean,
    Theorems.lean                AllInv proof: uncrossed + sorted (3,988 lines)
    TheoremsFull.lean            Remaining §13 invariants + trade guarantees;
                                 capstone `process_preserves_BookInvariant` (1,423 lines)
    TheoremsElegant.lean         Alternative proof of the uncrossed core (311 lines)
    TheoremsReachable.lean       Reachable-state corollary over order sequences (100 lines)
matcher_stl/                     Reference C++ (STL) implementation
paper.tex / paper.pdf            Paper manuscript
```

## Prerequisites

| Tool            | Version                                      | Notes |
| --------------- | -------------------------------------------- | ----- |
| Lean 4          | `leanprover/lean4:v4.26.0` (pinned)          | Install via `elan`, the toolchain is read automatically from `lean-toolchain`. |
| Lake            | Ships with Lean 4                            | Used for building, proof checking, and running `matchingengine`. |
| TLA+ Tools      | `tla2tools.jar` (TLC), 2023 release or later | Provides the `tlc2.TLC` model checker. |
| Java            | JDK 11+                                      | Required to run `tla2tools.jar`. |

### Installing Lean 4 via `elan`

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# Accept the defaults. From inside this repo, elan will auto-install
# the toolchain pinned in lean-toolchain (v4.26.0).
```

### Installing TLA+ tools

Download `tla2tools.jar` from
<https://github.com/tlaplus/tlaplus/releases> and set a convenience
variable:

```bash
export TLA_JAR=/path/to/tla2tools.jar
alias tlc='java -cp $TLA_JAR tlc2.TLC -deadlock'
```

`-deadlock` (equivalent to `CHECK_DEADLOCK FALSE`) is required: every
action in the model is guarded by `clock < MAX_CLOCK`, so exhausting the
clock budget is an expected terminal state under this bounded model, not
a real deadlock. Without it, TLC reports `Error: Deadlock reached` on
every configuration below instead of completing.

## Verification gate

For most purposes, don't run Lean/TLC/C++ separately — use the single
gate script, which runs the checks below in order and reports
`PASS`/`FAIL`/`SKIP` per layer (a skipped or timed-out layer is always
printed as `SKIP`, never as a pass):

```bash
./scripts/verify.sh          # fast gate: ~1-2 minutes
./scripts/verify.sh --full   # adds deep TLC exploration: ~45 min on a
                              # 24-core host for tiny/small/medium/amend
                              # (see matcher_tla/results/metadata.json for
                              # measured per-config times), plus a bounded
                              # 20-minute attempt at the 3-order (noamend)
                              # config, which has never completed
                              # exhaustively (see matcher_tla/REPORT.md)
                              # and is expected to report SKIP, not PASS.
```

`TLC_WORK` (default `~/.cache/matcher-tlc`) must be on real disk, not
`tmpfs` — the deep configs spill tens of millions of states to disk and
will die with "No space left on device" on a RAM-backed `/tmp`. Expect
several GB of scratch space under `--full` (removed automatically after
each config that completes).

What each layer reproduces:

| Layer | Reproduces |
|---|---|
| Lean proof closure (`lake build`, no-`sorry`, axiom check, `lake exe matchingengine`) | The proof-file statistics and capstone-theorem claims under "What is proved" above |
| TLC invariant coverage + smoke (fast gate) | The §13 invariant-suite claim in `matching-engine-formal-spec.md`; a fast regression, not the full state counts |
| TLC deep configs (`--full`): tiny/small/medium/amend | The model-checking statistics table in `paper.tex` (Table 4) — the four *completed* rows |
| TLC deep config (`--full`): 3-order/noamend, bounded | The "3-order (partial)" row in `matcher_tla/REPORT.md` — inconclusive by design, not a completed exploration |
| C++ correctness + conformance replay + shadow differential | The C++ engine claims and `matcher_stl/BUG_LOG.md` |
| WF differential | The Lean/TLA+ well-formedness agreement claim |

The fast gate is what CI runs on every push
(`.github/workflows/verify.yml`); `--full` is a separate,
manually-triggered workflow (`.github/workflows/verify_full.yml`)
because of its runtime — run it locally or via that workflow before a
release, or whenever you need to reconfirm the archived state counts in
`matcher_tla/results/`.

## Building and checking the Lean proofs

From inside `matcher_lean/`:

```bash
cd matcher_lean
lake build
```

This builds every file in the `MatchingEngine` library, including
`Theorems.lean`, `TheoremsFull.lean`, `TheoremsElegant.lean`, and
`TheoremsReachable.lean`, which are imported from the library root
`matcher_lean/MatchingEngine.lean`.
A successful `lake build` means every proof has been elaborated by
Lean with no open obligations.

To execute the runtime test suite in `Tests.lean`:

```bash
lake exe matchingengine
```

### What is proved

`matcher_lean/MatchingEngine/Theorems.lean` proves that `process`
preserves `AllInv` (uncrossed plus sorted on both sides):

```lean
theorem process_preserves_AllInv
    (b : BookState) (o : Order)
    (hpok  : OrderProcOk o)
    (hstops : StopsNoPostOnly b)
    (h : AllInv b) :
    AllInv (process b o).book
```

where

```
AllInv b ≡ BookUncrossed b
         ∧ bidsSortedDesc b
         ∧ asksSortedAsc  b.
```

`matcher_lean/MatchingEngine/TheoremsFull.lean` builds on this to prove
the remaining §13 book-state invariants — `NoGhosts`,
`StatusConsistency`, `NoRestingMarkets`, `NoRestingMTL`,
`NoRestingMinQty`, `NoEmptyLevels`, `FIFOWithinLevel` — plus two
unconditional trade-event guarantees, `PostOnlyGuarantee` and
`STPGuarantee`. It culminates in the capstone theorem:

```lean
theorem process_preserves_BookInvariant
    (b : BookState) (o : Order)
    (hall : AllInv b) (hpok : OrderProcOk o) (hsnp : StopsNoPostOnly b)
    (hb : BookOk b) (hstops : StopsWF b) (hok : OrderRestOk o) :
    BookInvariant (process b o).book
```

which combines the `AllInv` half proved in `Theorems.lean` with the
seven invariants proved in `TheoremsFull.lean`. Together with
`process_PostOnlyGuarantee` and `process_STPGuarantee` (which need no
book-state hypotheses at all), this is the paper's headline result and
covers every §13 invariant except:

- **INV-9** (passive-price execution): proved separately as
  `doMatch_passive_price` in `Theorems.lean`, but not composed into
  the capstone above.
- **INV-10** (event ordering): not modeled in Lean.

`matcher_lean/MatchingEngine/TheoremsReachable.lean` closes the
single-step-to-execution argument with the named corollary:

```lean
theorem process_all_preserves_BookInvariant (orders : List Order)
    (hwf : ∀ o ∈ orders, OrderProcOk o ∧ OrderRestOk o) :
    BookInvariant (orders.foldl processBook BookState.empty)
```

Thus every book reached from the empty book by a finite sequence of
orders satisfying those per-order hypotheses has `BookInvariant`.

All of the above holds for arbitrary finite book sizes satisfying the
stated hypotheses. The matching-loop fuel bound is derived from the
book state via `computeMatchFuel` and is proved sufficient, not
assumed — but this covers only `doMatch`'s inner loop. `process`
itself still drives the outer stop-trigger cascade with a fixed
`defaultFuel = 100` (see `Process.lean`); the theorems above hold even
on an exhausted-fuel branch, but that outer bound is not itself
state-derived.

`matcher_lean/MatchingEngine/TheoremsElegant.lean` gives a
complementary proof of `process_preserves_uncrossed` (the uncrossed
component of `AllInv`) via case analysis of the matching loop's
termination condition. It imports `Theorems.lean` and cites its
fuel-sufficiency result as a black box rather than re-deriving it, so
it is not an independent proof — but it is a genuinely different
decomposition of the same argument, and it is also built by
`lake build`.

## Running TLA+ / TLC

All runs are from the repository root. The configurations are
summarised in `matcher_tla/REPORT.md` and in Table 4 of the paper.

### Medium configuration (default)

2 orders, 3 prices, `MAX_QTY = 2`, `MAX_CLOCK = 4`, amend disabled.
Explores roughly 49.7 M states generated / 29.6 M distinct in
~14 minutes (freshly reproduced 2026-09-26; see
`matcher_tla/results/metadata.json` for exact provenance and historical
comparison).

```bash
tlc -config matcher_tla/MatchingEngine.cfg matcher_tla/MatchingEngine.tla
```

### 3-order configuration

3 orders, 2 prices. Larger state space; used for exploratory runs.

```bash
tlc -config matcher_tla/MatchingEngine_noamend.cfg matcher_tla/MatchingEngine.tla
```

### With amend action

2 orders, 2 prices (a narrower price domain than the medium
configuration's 3 prices), with the `AmendOrder` action enabled.

```bash
tlc -config matcher_tla/MatchingEngine_amend.cfg matcher_tla/MatchingEngine.tla
```

### Checked invariants

Every configuration checks the same invariant suite:

```
BookUncrossed, NoEmptyLevels, NoGhosts, StatusConsistency,
FIFOWithinLevel, NoRestingMarkets, PostOnlyGuarantee, STPGuarantee,
NoRestingMTL, NoRestingMinQty
```

Each invariant corresponds to a numbered clause in
`matching-engine-formal-spec.md` §13. On a clean run TLC reports no
violations.

## Reproducing the findings

### Bug #1: FIFO violation via stale stop-trigger timestamp

Revert the timestamp refresh in `ProcessTriggeredStops`: replace

```
[ConvertStop(s) EXCEPT !.timestamp = tm]
```

with

```
ConvertStop(s)
```

in `matcher_tla/MatchingEngine.tla`, then re-run TLC with the `_noamend`
configuration:

```bash
tlc -config matcher_tla/MatchingEngine_noamend.cfg matcher_tla/MatchingEngine.tla
```

TLC produces a `FIFOWithinLevel` violation (freshly reproduced
2026-09-26: 9,160,154 states generated / 4,980,329 distinct states,
2m41s wall time — hardware/JVM-dependent, not a universal constant; raw
log in `matcher_tla/results/`). This is a three-order counterexample;
no minimization procedure was run, so it is not claimed to be minimal.
See `matcher_tla/REPORT.md` and §6.1 of the paper.

### Bug #2: Iceberg stranding under STP DECREMENT

Remove the reload-after-DECREMENT clause from the STP path in
`matcher_tla/MatchingEngine.tla`. The specification gap is described in
`matcher_tla/REPORT.md` and §6.2 of the paper.

### Constant-fuel unsoundness (found during the Lean proof)

`computeMatchFuel` (state-derived, proved sufficient) and `defaultFuel`
(the constant `100`) already coexist in
`matcher_lean/MatchingEngine/Process.lean` — `defaultFuel` bounds only
the outer stop-cascade recursion. To reproduce the historical bug,
change which one gates the inner matching loop: in `processOrder`,
replace the fuel argument at each of the three `matchOrder
(computeMatchFuel b order.side) ...` call sites, and the
`doMatch (computeMatchFuel b' converted.side) ...` call in the MTL
second-pass branch, with the constant `defaultFuel`. Then re-run (from
inside `matcher_lean/`):

```bash
lake build
```

The proof of `doMatch_preserves_AllInv` fails because the measure
argument no longer dominates the recursive call bound. The concrete
counterexample is a book with more than 100 contra-side orders; see
§7.2 of the paper.

### Build-closure incident

Delete `import MatchingEngine.Theorems` from
`matcher_lean/MatchingEngine.lean` and run `lake build` from inside
`matcher_lean/`. The build succeeds, but `Theorems.lean` is not
elaborated on that run. Adding the import back restores full proof
checking. This is discussed in §7.3 of the paper.

## Building the paper

```bash
make paper
```

Requires `pdflatex` (the bibliography is a plain `thebibliography` block,
not an external `.bib` database, so no `bibtex`/`biber` pass is needed).
The `Makefile` runs two `pdflatex` passes so cross-references (section and
table numbers) stabilize; a third pass produces byte-identical text output
to the second, so two passes are sufficient. `make paper-clean` removes
the `.aux`/`.log`/`.out`/`.toc` build byproducts.

## Citing

If you reference this work, please cite the accompanying paper
(`paper.pdf`): "From Bounded Model Checking to Mechanized Proof: A
Multi-Level Verification Case Study for a Price-Time Priority
Matching Engine."

## License

MIT — see `LICENSE`.
