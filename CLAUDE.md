# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repo is

A multi-level verification case study for a price-time priority matching engine. The artifact is a paper (`paper.tex` / `paper.pdf`) backed by three coordinated implementations of the same matcher:

- `matcher_tla/` — TLA+ specification + TLC bounded model checking. Authoritative for action semantics.
- `matcher_lean/` — Lean 4 reference implementation with a mechanized proof that `process` preserves `AllInv` (uncrossed + sorted bids/asks). Authoritative for invariant preservation.
- `matcher_stl/` — Header-only C++17 production engine (`src/engine.h`). Verified against the other two via conformance replay (TLA traces) and shadow differential testing (random ops vs. a vector-based reference).
- `matching-engine-formal-spec.md` — prose spec v1.2.0; numbered clauses (§13) match TLA invariant names.

The three implementations are not independent codebases — they are the same matcher at three abstraction levels, and changes typically need to land in all three (or be deliberately scoped to one).

## Common commands

### Lean (from `matcher_lean/`)
```bash
lake build                  # Build library + check ALL proofs (Theorems.lean, TheoremsElegant.lean)
lake exe matchingengine     # Run runtime test suite from Tests.lean
```
A clean `lake build` is the proof-checking signal. CI runs this via `.github/workflows/lean_action_ci.yml`.

### TLA+ / TLC (from repo root, with `tla2tools.jar` available)
```bash
alias tlc='java -cp "$TLA_JAR" tlc2.TLC'

# Three primary configs:
tlc -config matcher_tla/MatchingEngine.cfg          matcher_tla/MatchingEngine.tla   # 2 orders / 3 prices, no amend (medium, ~36.7M states)
tlc -config matcher_tla/MatchingEngine_noamend.cfg  matcher_tla/MatchingEngine.tla   # 3 orders / 2 prices
tlc -config matcher_tla/MatchingEngine_amend.cfg    matcher_tla/MatchingEngine.tla   # medium + AmendOrder enabled
```
Scenario-specific specs and per-target configs live in `matcher_tla/` (e.g. `MatchingEngine_iceberg_resting.tla` + `iceberg_resting__TargetNoTrade.cfg`). The seeded experiment driver is `matcher_tla/run_experiments.sh fast|deep`, launched detached via `matcher_tla/launch.sh`.

### C++ engine (from `matcher_stl/`)
The engine is header-only; CMake produces four binaries (`test_correctness`, `test_performance`, `conformance_harness`, `shadow_test`).

```bash
cmake -B build  -S . -DCMAKE_BUILD_TYPE=Release && cmake --build build  -j
./build/test_correctness                  # unit tests
./build/test_performance                  # benchmark (-O3 -march=native)
./build/shadow_test <steps> <seed>        # random differential vs vector-based reference
./build/conformance_harness <trace.json>  # replay a TLC counterexample trace

# Bulk runs:
./tools/shadow_sweep.sh [SEEDS] [STEPS] [JOBS] [OUT_DIR]            # parallel seeded shadow sweep (uses build-verify/)
./tools/shadow_coverage_sweep.sh [SEEDS] [STEPS] [OUT_DIR]          # serial under gcov, produces gcovr report (uses build-coverage/)
```

There are three parallel build trees by convention:
- `build/` — default Release build for ad-hoc work.
- `build-verify/` — Release build used by `shadow_sweep.sh`.
- `build-coverage/` — gcov-instrumented build used by `shadow_coverage_sweep.sh`.

## Reproducing the paper's findings

The README lists three reproducible defect scenarios; when working on them, use these commands verbatim:
- **Bug #1 (FIFO via stale stop timestamp)** — revert the `EXCEPT !.timestamp = tm` in `ProcessTriggeredStops` (`matcher_tla/MatchingEngine.tla`) → expect `FIFOWithinLevel` violation under the `_noamend` config.
- **Bug #2 (iceberg stranding under STP DECREMENT)** — remove the reload-after-DECREMENT clause in the STP path of the same file.
- **Constant-fuel unsoundness** — replace `computeMatchFuel` with `defaultFuel := 100` in `matcher_lean/MatchingEngine/Process.lean` → `lake build` fails on `doMatch_preserves_AllInv`.
- **Build-closure incident** — remove `import MatchingEngine.Theorems` from `matcher_lean/MatchingEngine.lean`; `lake build` succeeds but skips the proof file.

C++ implementation defects discovered via the conformance/shadow pipelines are tracked separately in `matcher_stl/BUG_LOG.md` with stable `CPP-NNN` IDs (currently CPP-001..005).

## Architecture notes that span files

- **The Lean main theorem is `process_preserves_AllInv` in `matcher_lean/MatchingEngine/Theorems.lean`** (constructive, ~3,986 lines). `TheoremsElegant.lean` is an independent structural proof of the same statement. Both must build for the verification claim to hold. The matching-loop fuel is *derived* from book state via `computeMatchFuel`, not assumed — that's load-bearing for soundness.
- **The TLA spec uses numbered invariants matching the prose spec** (`BookUncrossed`, `NoGhosts`, `StatusConsistency`, `FIFOWithinLevel`, `NoRestingMarkets`, `PostOnlyGuarantee`, `STPGuarantee`, `NoRestingMTL`, `NoRestingMinQty`). Every TLC config checks the full suite. New invariants belong in both `MatchingEngine.tla` and `matching-engine-formal-spec.md` §13.
- **The TLA→C++ contract lives in `matcher_stl/tools/conformance/MAPPING.md`.** Every field/enum mapping the conformance harness relies on is documented there. When adding actions or fields to the TLA spec, update MAPPING.md and the converter (`convert_matching_traces.py`) before changing the harness.
- **The shadow test's reference engine is a literal vector-based implementation of the spec** (in `tools/conformance/shadow_test.cpp`). When the real engine and the reference disagree, default to assuming the real engine is wrong — but check whether the reference itself models the spec correctly (CPP-004 was a reference modelling error, not an engine bug).

## Project-specific conventions

- **`matcher_stl/BUG_LOG.md` is the source of truth for C++ engine defects, not `paper.tex`.** Every fix to `matcher_stl/src/engine.h` (or neighbours) must land a `CPP-NNN` entry with: deterministic repro (seed+step or trace), symptom, root cause, diff, verification runs, and *why earlier suites missed it*. The paper's §5 is lifted from this file at revision time.
- **Only engine-vs-spec defects count as paper findings.** Bugs in the harness, the TLA→JSON converter (`convert_matching_traces.py`), test scaffolding, or build scripts are dev-process noise — fix them, mention in the commit, but do **not** add them to `BUG_LOG.md` or count them in defect totals. Known false-positive class: `infer_fills` in the converter collapses iceberg slice reloads into one fill (TLA has no `trades` state variable); those divergences are not engine bugs.
- **Spec-level / TLA / Lean defects** (e.g. the two reproducible bugs above) are documented directly in `paper.tex` §5, not `BUG_LOG.md`.
- **No coauthor or Claude attribution in commits or files.**
