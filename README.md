# Verified Matching Engine

A feature-rich price-time priority matching engine verified at two
levels: bounded exhaustive state-space exploration with TLA+/TLC, and
a mechanized proof in Lean 4 that the processing pipeline preserves
the combined book invariant `AllInv` (uncrossed plus sorted on both
sides).

The full write-up is in `paper.tex` / `paper.pdf`. This README
describes how to build and run the two verification artifacts.

## Repository layout

```
matching-engine-formal-spec.md   Prose specification (v1.2.0, 978 lines)
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
    Theorems.lean                Constructive proof (3,986 lines)
    TheoremsElegant.lean         Structural proof (312 lines)
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
alias tlc='java -cp $TLA_JAR tlc2.TLC'
```

## Building and checking the Lean proofs

From inside `matcher_lean/`:

```bash
cd matcher_lean
lake build
```

This builds every file in the `MatchingEngine` library, including
`Theorems.lean` and `TheoremsElegant.lean`, which are imported from
the library root `matcher_lean/MatchingEngine.lean`. A successful
`lake build` means every proof has been elaborated by Lean with no
open obligations.

To execute the runtime test suite in `Tests.lean`:

```bash
lake exe matchingengine
```

### What is proved

The main theorem lives in `matcher_lean/MatchingEngine/Theorems.lean`:

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

The theorem holds for arbitrary book sizes. The matching-loop fuel
bound is derived from the book state via `computeMatchFuel` and is
proved sufficient, not assumed.

`matcher_lean/MatchingEngine/TheoremsElegant.lean` contains an independent proof
of the same result via case analysis of the matching termination
condition; it is also built by `lake build`.

## Running TLA+ / TLC

All runs are from the repository root. The configurations are
summarised in `matcher_tla/REPORT.md` and in Table 4 of the paper.

### Medium configuration (default)

2 orders, 3 prices, `MAX_QTY = 2`, `MAX_CLOCK = 4`, amend disabled.
Explores roughly 36.7 M states in a few minutes.

```bash
tlc -config matcher_tla/MatchingEngine.cfg matcher_tla/MatchingEngine.tla
```

### 3-order configuration

3 orders, 2 prices. Larger state space; used for exploratory runs.

```bash
tlc -config matcher_tla/MatchingEngine_noamend.cfg matcher_tla/MatchingEngine.tla
```

### With amend action

Same scope as the medium configuration, but the `AmendOrder` action
is enabled.

```bash
tlc -config matcher_tla/MatchingEngine_amend.cfg matcher_tla/MatchingEngine.tla
```

### Checked invariants

Every configuration checks the same invariant suite:

```
BookUncrossed, NoGhosts, StatusConsistency, FIFOWithinLevel,
NoRestingMarkets, PostOnlyGuarantee, STPGuarantee, NoRestingMTL,
NoRestingMinQty
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

TLC produces a `FIFOWithinLevel` violation within the first few
million states. The minimal counterexample is a three-order
sequence; see `matcher_tla/REPORT.md` and §6.1 of the paper.

### Bug #2: Iceberg stranding under STP DECREMENT

Remove the reload-after-DECREMENT clause from the STP path in
`matcher_tla/MatchingEngine.tla`. The specification gap is described in
`matcher_tla/REPORT.md` and §6.2 of the paper.

### Constant-fuel unsoundness (found during the Lean proof)

Revert `computeMatchFuel` in `matcher_lean/MatchingEngine/Process.lean` to the
constant

```lean
def defaultFuel : Nat := 100
```

and re-run (from inside `matcher_lean/`):

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

## Citing

If you reference this work, please cite the accompanying paper
(`paper.pdf`): "From Bounded Model Checking to Mechanized Proof: A
Multi-Level Verification Case Study for a Price-Time Priority
Matching Engine."

## License

See repository metadata on GitHub.
