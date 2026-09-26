# Publication Audit and Remediation Checklist

Audit date: 2026-09-26  
Audited revision: `faf9e4d` (`master`)  
Primary manuscript: `paper.tex` / `paper.pdf`

## Purpose

This document records the pre-publication fact check of the paper and its
supporting repository. It is intended to be an actionable checklist for a
revision pass and a stable basis for a later re-audit.

The paper has a real, potentially publishable core: the Lean proof artifacts
build, the principal theorems exist, and the C++/TLA testing infrastructure is
substantial. It should not be submitted in its current state, however, because
several experimental and reproducibility claims are inconsistent with the
checked-in artifacts, and the repository's own verification gate currently
fails.

Recommended venue after remediation: **TACAS 2027, case-study paper**. The
official deadline is 2026-10-15 AoE, and the paper must be converted to the
18-page LNCS format (bibliography excluded). Artifact evaluation is optional
for case-study papers but strongly recommended.

Official venue pages:

- <https://etaps.org/2027/conferences/tacas/>
- <https://etaps.org/2027/cfp/>

## Audit baseline

The following checks passed on the audited revision:

- `lake build` reached and checked all three proof files.
- No proof source contained `sorry`.
- The inspected top-level theorems did not depend on `sorryAx`.
- `lake exe matchingengine` reported 17 tests passed.
- The TLC smoke configuration explored 548,397 distinct states without an
  invariant violation.
- The C++ suite reported 65 passed and 0 failed.
- The conformance harness replayed 10 traces / 21 steps successfully.
- `shadow_test 2000 1` passed.
- The principal capstone and trade theorems exist:
  `process_preserves_BookInvariant`, `process_PostOnlyGuarantee`, and
  `process_STPGuarantee`.
- The paper's proof-file statistics were exact at the audited revision:

  | File | Lines | theorem/lemma declarations |
  |---|---:|---:|
  | `Theorems.lean` | 3,965 | 74 |
  | `TheoremsFull.lean` | 1,423 | 77 |
  | `TheoremsElegant.lean` | 311 | 6 |

These confirmed points should be retained, subject to the qualifications
below.

## Submission blockers

### P0-1: Make the repository verification gate pass

Status: **blocking**

Running:

```bash
./scripts/verify.sh
```

ended with one failure in the Lean/TLA well-formedness differential. The
failure was infrastructure-level: TLC rejected the combined modules because
`WFShapes` was defined both in `MatchingEngine.tla` and `WFEmit.tla`:

```text
Operator WFShapes already defined or declared.
```

This appears to have arisen when `WFShapes` was hoisted into the main model.
It does not by itself demonstrate a semantic disagreement between Lean and
TLA+, but it means the claimed cross-artifact check is currently not running.

Required fix:

- Remove or rename the duplicate definition without creating a second,
  drifting copy of the well-formedness domain.
- Ensure `scripts/wf_differential.sh` compares the two accepted shape sets.
- Ensure failure output is preserved or printed rather than being swallowed
  by `set -e`.

Acceptance test:

```bash
./scripts/verify.sh
```

must exit zero with no failed layers. Skips must be explicitly disclosed; a
skipped deep TLC run is not a pass.

### P0-2: Resolve the impossible Small-configuration counterexample

Status: **blocking**

The paper's FIFO counterexample submits three orders (IDs 1, 2, and 3), but it
claims the counterexample occurred in and can be reproduced with a Small
configuration having `MAX_ORDERS = 2`.

In `MatchingEngine.tla`, `SubmitOrder` is enabled only while
`nextId <= MAX_ORDERS`; consequently, `MAX_ORDERS = 2` permits only two total
submissions. The printed three-order trace cannot occur in that configuration.
The currently checked-in three-order configuration is
`MatchingEngine_noamend.cfg`, with `MAX_ORDERS = 3`.

Affected claims include:

- the exact counterexample trace;
- the Small-row discovery claim in Table 4;
- the claim that the first counterexample appeared in 102 seconds;
- the minimality claim;
- the reproduction instructions near the end of the paper;
- parallel claims in `REPORT.md` and `README.md`.

Required fix:

1. Create a clean pre-fix variant by reverting only the timestamp refresh.
2. Run TLC with the exact configuration that actually produces the trace.
3. Save the raw output, exact config, exact model/patch, TLC version, JVM
   command, host information, and counterexample trace in a stable results
   directory.
4. Correct every table, runtime, bound, and reproduction instruction to match
   that run.
5. Do not call the trace minimal unless minimality is established by a stated
   procedure. Otherwise call it "a three-order counterexample."

Acceptance test:

- A command copied verbatim from the paper must reproduce the documented FIFO
  violation from a fresh checkout.
- The archived trace must have no order ID greater than the configured
  `MAX_ORDERS`.

### P0-3: Archive evidence for all historical TLC statistics

Status: **blocking**

The repository currently gives narrative counts and runtimes in `REPORT.md`
and `paper.tex`, but does not contain complete original TLC logs supporting all
of the reported completed and partial runs. The current main model is post-fix,
so it cannot itself establish the historical bug-discovery claims.

Required fix:

- Archive full raw logs for every row retained in the paper.
- Record TLC version, Java version, command, worker count, host, elapsed time,
  generated states, distinct states, queue depth, result, model hash, and
  config hash.
- Include the interrupted three-order run's termination method and raw log.
- Include the pre-fix counterexample run separately from the post-fix clean
  run.
- Add a script that regenerates a machine-readable summary used to populate
  the paper table.

If evidence cannot be recovered, remove the unsupported exact runtimes and
counts and rerun the experiments.

### P0-4: Correct state-count terminology and arithmetic

Status: **blocking**

The manuscript uses "generated," "reachable," and "distinct" states
interchangeably. Its own table reports:

- completed-run distinct total: 37,527,810;
- completed-run generated total: 76,417,685;
- Medium: 36,700,016 generated but 21,261,901 distinct;
- partial three-order: more than 26 million additional distinct states.

Thus "configurations totaling 36 million reachable states" does not cleanly
describe the table.

Required fix:

- Select a single accurately named metric for headline use.
- Prefer wording such as: "The four completed configurations explored 37.5
  million distinct states in aggregate."
- State that summing per-run distinct counts measures aggregate exploration
  workload, not the cardinality of a deduplicated union across configurations.
- Use "generated" only for TLC's generated-state count.
- Treat the incomplete three-order run separately.

### P0-5: Narrow the fuel claim

Status: **blocking**

The inner matching loop now uses `computeMatchFuel`, and its sufficiency is
proved. However, `process` still calls `processOrder defaultFuel`, and
`defaultFuel` remains 100. The outer stop/cascade recursion is therefore still
fuel-bounded.

This does not invalidate invariant preservation: exhausted-fuel branches
return a safe book. It does mean the manuscript must not imply that the entire
processing pipeline has a state-derived, semantically complete recursion
bound.

Required manuscript distinction:

- `doMatch`: state-derived fuel, with sufficiency/progress proof;
- `processOrder` / stop cascade: still invoked with `defaultFuel = 100`;
- invariant preservation: proved even if outer fuel is exhausted;
- completion of arbitrarily long trigger cascades: not established unless a
  separate theorem or derived bound is added.

Also correct the reproduction instruction that says to "replace
`computeMatchFuel` with `defaultFuel := 100`"; these are different existing
definitions. Provide an exact patch instead.

### P0-6: State exactly which §13 properties Lean proves

Status: **blocking**

The strongest accurate claim is that Lean proves all modeled §13 book-state
invariants plus post-only and STP guarantees on emitted trades.

Qualifications that must remain visible wherever the result is summarized:

- INV-10 (event ordering) is not modeled in Lean.
- INV-9 (passive-price execution) is described as holding by construction, not
  as a separately stated checked theorem in the capstone.
- The main result has explicit hypotheses: `AllInv`, `OrderProcOk`,
  `StopsNoPostOnly`, `BookOk`, `StopsWF`, and `OrderRestOk`.
- The execution-level corollary applies to finite books reachable from an
  empty book under appropriately well-formed incoming orders; it is not a
  theorem about literally every unconstrained input value.

Recommended wording:

> Lean proves preservation of all modeled §13 book-state invariants for
> arbitrary finite books satisfying the stated preconditions, plus unconditional
> post-only and STP guarantees on emitted trades. INV-9 is enforced by trade
> construction; INV-10 is outside the Lean model.

Do not use an unqualified "the full §13 invariant suite" or "all possible
inputs of all sizes."

### P0-7: Remove the claim that the Lean/specification semantic gap is zero

Status: **blocking**

It is correct that the Lean tests and theorems operate on the same Lean
definitions, so there is no extraction or separate-executable gap inside the
Lean artifact. It is not correct to say the overall semantic gap is zero. The
paper's own MTL/MinQty transcription defect demonstrates that prose-to-Lean
correspondence remains a validation obligation.

Recommended replacement:

> There is no code-extraction or model-to-executable gap inside the Lean
> artifact; correspondence between the prose specification and its Lean
> transcription remains a separate validation obligation.

### P0-8: Stop calling the elegant proof independent

Status: **blocking**

`TheoremsElegant.lean` imports `MatchingEngine.Theorems` and reuses the
constructive development. It is a useful alternative structural argument but
not independent in the assurance sense.

Replace "independent proof" with:

> a complementary proof of the uncrossedness core, reusing lemmas from the
> constructive development.

Describe precisely which final theorem is reproved and which imported lemmas
remain in its dependency footprint.

## Major factual and wording corrections

### P1-1: Correct introductory order semantics

- **Market:** "Executes immediately or not at all" is incorrect for an
  ordinary market order. A market order can execute partially and have its
  remainder canceled. "Not at all" suggests FOK semantics.
- **Limit:** "Will wait indefinitely" ignores IOC, DAY, GTD, cancellation,
  and expiry. Say that a residual *may rest, subject to time-in-force*.
- **MinQty:** Present the described first-fill behavior as this specification's
  semantics, not as a universal exchange definition.
- **Iceberg reload priority:** Likewise identify losing priority on reload as
  the modeled policy; venue rules can differ.

### P1-2: Remove unsupported industry universals

Revise or source the following:

- "Every exchange ... runs a matching engine at its core." Prefer
  "continuous limit-order-book exchanges typically use a matching engine."
- "Every second, it processes thousands ..." Either source it or remove the
  numerical generalization.
- "Every such error is a financial event with an identifiable winner and
  loser." This is rhetoric, not an established universal.
- "Production engines hold millions of orders at prices across a continuous
  range." Prices are normally on discrete tick grids. Use "large discrete
  price domains" and source any capacity claim.

### P1-3: Recast rhetorical absolutes as observations

The following are conclusions or motivations, not facts established by the
artifact:

- "Each individual feature is correctly specified in isolation."
- "The bugs live in intersections that prose review cannot see."
- "No single human reviewer is likely to hold [the cases] in mind."
- "Only a specification rooted outside C++ can" find shared semantic errors.

Use calibrated formulations such as "in this case study," "can be difficult
to detect," and "the spec-rooted oracle detected an error shared by the two
C++ implementations."

### P1-4: Keep the iceberg finding at the correct claim level

The paper correctly says in one place that the STP-DECREMENT/iceberg problem
was identified during modeling/specification review and that the checked TLA+
model already contained the repair. Elsewhere it says TLC produced both
feature-composition defects as concrete traces.

Use one consistent account:

- FIFO timestamp issue: TLC counterexample, once reproduced and archived;
- iceberg reload issue: specification gap found during operational modeling,
  illustrated by a scenario, not a TLC invariant counterexample unless an
  actual pre-fix checked trace is added.

### P1-5: Substantiate the MTL/MinQty transcription finding

Archive an exact pre-fix Lean/TLA patch or commit and a concrete witness. State
precisely:

- what the prose specification required;
- how the Lean and TLA transcriptions differed;
- which theorem/proof obligation exposed the divergence;
- how the repaired artifacts now agree;
- whether the C++ implementation ever had the same defect.

Avoid relying solely on retrospective narrative.

### P1-6: Make conformance-scale claims reproducible

The paper reports approximately 232,000 traces and 1.5 million per-step
comparisons across twelve scenarios. The fast verification gate currently
checks only 10 stored JSON traces and 21 steps.

Required fix:

- Add a manifest and summary generator for the large experiment corpus.
- Record scenario count, seeds/chunks, traces, valid converted traces, replayed
  steps, excluded traces, failures, tool versions, and commands.
- Explain clearly that the fast gate checks a small deterministic regression
  subset while the large experiment is a separately archived evaluation.
- Ensure "twelve scenarios" matches the scenario files actually included in
  the counted experiment.
- Correct or remove "tens of millions of operations per seed" unless the logs
  support that exact unit and scale.

### P1-7: Qualify differential-testing conclusions

An independent reference does not "catch all data-structure bugs" that differ
between implementations; finite randomized testing cannot provide an "all"
guarantee. Replace with:

> Differential testing can detect sampled behavioral disagreements, but it
> cannot detect an error on an exercised path when both implementations produce
> the same erroneous observable behavior.

### P1-8: Clarify proof independence and trusted computing base

- Preserve the verified axiom output in a checked-in generated report or make
  it part of CI.
- Say "standard axioms used by this Lean development" rather than implying
  that these three axioms constitute Lean's entire classical core.
- The Lean kernel and compiler/toolchain remain part of the trusted computing
  base; "unusually small base" is a comparative judgment and should be
  justified or softened.
- `omega` is a tactic that produces proof terms checked by the kernel. The
  manuscript's claim that no external solver participates in acceptance is
  reasonable, but phrase it specifically in terms of kernel-checked proof
  terms.

### P1-9: Align README, report, paper, and source

At the audited revision, `README.md` was stale or incomplete in several ways:

- it reported older line counts for `Theorems.lean` and
  `TheoremsElegant.lean`;
- it omitted `TheoremsFull.lean` from the repository layout and proof summary;
- it described only the `AllInv` theorem while the paper emphasized the later
  capstone;
- it said the amend configuration had the same scope as Medium, although
  Medium uses three prices and Amend uses two;
- its displayed invariant list omitted `NoEmptyLevels`;
- it called the prose spec 978 lines while the audited file had 979.

Generate simple counts where practical and make one file the canonical source
for experiment metadata.

### P1-10: Verify every bibliography entry and every related-work comparison

For each bibliography item:

- verify authors, exact title, venue, year, volume/issue, pages or article
  number, and DOI/official URL against the publisher or proceedings;
- update preprints to published versions where appropriate;
- ensure every entry is cited and every citation key resolves;
- avoid `et al.` in the bibliography if the target style expects a complete
  author list;
- confirm that claims such as "most recently," "early result," "largest," and
  "closest methodological analogue" remain accurate as of submission;
- explain the concrete difference between this work and the closest verified
  continuous-double-auction work, rather than relying on broad object/method
  labels.

The related-work section is directionally strong, but novelty should be framed
as an applied multi-method case study, not as a new general proof technique,
model checker, matching algorithm, or end-to-end refinement method.

## Reproducibility and artifact hygiene

### P1-11: Create one authoritative reproduction entry point

The artifact should provide:

```bash
./scripts/verify.sh          # bounded, reasonably fast regression gate
./scripts/verify.sh --full   # all paper table runs or an explicit documented subset
```

The README must state estimated runtime, memory, disk usage, architecture, and
which paper claims each command reproduces. A command that skips a layer must
say `SKIPPED`, never `PASSED`.

### P1-12: Add CI coverage for the actual claims

CI should at minimum check:

- Lean build and runtime tests;
- no `sorryAx` in top-level results;
- proof files are reachable from the default target;
- bibliography/citation and LaTeX compilation;
- C++ build and directed tests;
- deterministic conformance regressions;
- WF differential;
- TLC invariant/config coverage;
- TLC smoke run.

Deep experiments may remain scheduled/manual if resources are documented and
their immutable outputs are archived.

### P1-13: Deposit a permanent artifact

GitHub is public but is not by itself a versioned archival citation. Before
publication:

- create a clean tagged release;
- deposit the release on Zenodo or another accepted long-term repository;
- cite the DOI and exact version in the paper;
- include an explicit license for code, paper, and data;
- add a data-availability statement required by ETAPS;
- include checksums for large result bundles.

### P1-14: Remove repository debris and clarify tracked results

Remove AppleDouble and OS metadata files such as:

- `._paper.pdf`;
- `._claude-code-prompt.md`;
- `.DS_Store` and nested variants;
- `._engine.h`, `._types.h`, and similar files.

Do not blindly delete experimental evidence. Decide which logs/results support
the paper, organize them under a documented results directory, and exclude
only redundant build products and personal filesystem metadata.

### P1-15: Ensure the PDF is generated from the committed source

The audited worktree already had a modified `paper.pdf`. Before release:

- use a deterministic documented build command;
- rebuild twice or use `latexmk` so references stabilize;
- ensure `git diff --exit-code paper.pdf` after the documented build;
- fill PDF title, author, subject, and keywords metadata where appropriate;
- resolve overfull boxes and font substitution warnings.

## Manuscript-specific edits

### P2-1: Title and headline positioning

The current title is plausible, but the repository name and some prose invite
an end-to-end interpretation not supported by the artifact. Consider:

> Bounded Model Checking, Mechanized Invariants, and Conformance Testing for a
> Price-Time Matching Engine

The defensible central claim is:

> A case study showing how bounded TLA+ exploration, Lean invariant
> preservation, and model-based C++ conformance testing expose different
> classes of matching-engine defects.

Do not call the C++ implementation formally verified. There is no general
Lean-to-C++ or TLA-to-C++ refinement theorem.

### P2-2: Rewrite the abstract after evidence is repaired

The abstract should distinguish:

- one archived TLC counterexample;
- one specification gap found during modeling;
- one inner-loop fuel/sufficiency issue exposed during proof development;
- one MTL/MinQty transcription defect;
- one C++ defect found by spec-rooted trace conformance;
- exactly what Lean proves and excludes;
- absence of end-to-end refinement.

Avoid unsupported state totals and discovery-attribution language.

### P2-3: Shorten the tutorial material

For an 18-page TACAS case-study submission, substantially compress:

- the general explanation of buying and selling;
- the order-book ASCII example;
- repeated explanations of model checking versus theorem proving;
- repeated restatements of the five findings;
- lengthy general related-work surveys not needed for positioning.

Use the saved space for:

- exact formal statements;
- experiment provenance;
- assurance boundaries;
- defect witnesses;
- cross-artifact mapping;
- limitations.

### P2-4: Use precise theorem/corollary language

Separate:

1. single-step preservation theorems with explicit hypotheses;
2. base-state lemmas;
3. preservation of auxiliary hypotheses;
4. the induction yielding a reachable-execution corollary.

If the paper claims that the complete hypothesis bundle holds on every
reachable state, state or cite the exact Lean theorem that composes these
facts. Do not leave the execution-level conclusion as prose assembled from
separate lemmas if a reviewer cannot check the composition directly.

### P2-5: Correct date and acknowledgments

- Replace ambiguous `04/11/2026` with an unambiguous written or ISO date.
- Remove "We thank the anonymous reviewers" before the paper has actually
  received anonymous reviews.
- Ensure employer approval and author/affiliation details are correct.
- Retain the LLM-assistance disclosure, but make factual authorship and
  contribution claims only to the extent documented by the author.

### P2-6: Explain model scope without overgeneralizing

State explicitly:

- prices are a finite configured set;
- quantities and submission count are bounded;
- only one non-null STP group identifier is modeled in the main exploration;
- GTD timing is simplified;
- event ordering is not modeled;
- completed versus interrupted configurations;
- TLC verifies the TLA model, not the prose or C++ implementation;
- conformance compares projected observables only.

### P2-7: Fix table and invariant nomenclature

- Use the canonical INV numbering from the prose spec consistently.
- Do not conflate sortedness with `BookUncrossed` in TLA reporting.
- `NoEmptyLevels` is explicitly checked in current configs, not merely absent
  from the inventory.
- Distinguish "trivial by representation/construction" from "checked as a TLC
  invariant" and from "proved as a Lean proposition."
- Include INV-10 in a complete inventory with an explicit "not modeled"
  status rather than silently omitting it from the Lean/TLC table.

### P2-8: Calibrate effort and cost claims

Claims such as "two days," "four weeks," "weeks, not years," and which parts
were human versus model contributions are not derivable from the code. Retain
them only if the author can substantiate them from development records and is
comfortable defending them. Label them as reported engineering effort, not
experimental measurements.

## Venue plan

### Primary: TACAS 2027 case-study paper

Why it fits:

- specification and verification techniques;
- theorem proving and model checking;
- testing and conformance;
- an application/case study with broader methodological lessons;
- a substantial evaluable artifact.

Submission constraints checked on 2026-09-26:

- deadline: 2026-10-15 AoE;
- format: Springer LNCS;
- limit: 18 pages plus bibliography and optional appendix;
- data-availability statement required;
- case-study artifact evaluation is voluntary but strongly recommended;
- case-study papers are not within TACAS's regular-paper-only double-blind
  rule, but all current official instructions should be rechecked immediately
  before submission.

### Secondary: iFS 2027 empirical-evaluation paper

iFS is plausible if the paper is reframed around evaluation of the multi-layer
workflow. Its long-paper limit is 16 pages plus two pages of references, so it
requires even more compression.

### Journal fallback

If the historical experiments cannot be rerun and archived before the
conference deadline, do not rush the submission. A substantially revised
journal version could be considered for *Formal Methods in System Design* or,
if the mechanized-reasoning contribution is strengthened and foregrounded,
the *Journal of Automated Reasoning*. Venue scope and current submission terms
must be rechecked at the time of submission.

## Final re-audit checklist

The next audit should not sign off until all applicable items below pass.

- [ ] Clean working tree or all intentional generated changes explained.
- [ ] `./scripts/verify.sh` exits zero with no unexplained skips.
- [ ] Full/deep TLC runs either reproduced or backed by immutable raw logs.
- [ ] FIFO bug reproduction command works exactly as printed.
- [ ] Counterexample configuration permits every order in the trace.
- [ ] Historical defect variants/patches and witnesses are archived.
- [ ] State counts and runtimes are generated from archived logs.
- [ ] Generated/distinct/reachable terminology is consistent.
- [ ] WF differential runs and reports identical accepted shape sets, or any
      genuine semantic difference is documented and fixed.
- [ ] Inner match fuel and outer cascade fuel are distinguished everywhere.
- [ ] No unqualified claim of the full §13 suite where INV-10 is excluded.
- [ ] No claim of zero prose-to-Lean semantic gap.
- [ ] Elegant proof described as complementary, not independent.
- [ ] All theorem hypotheses and reachable-state qualifications are retained.
- [ ] Large conformance experiment has a manifest and reproducible summary.
- [ ] README, REPORT, source, tables, and paper agree.
- [ ] Every citation checked against an authoritative bibliographic source.
- [ ] Every empirical or historical number has preserved evidence.
- [ ] No universal market-structure claims without a source or qualification.
- [ ] Paper converted to the chosen venue template and page limit.
- [ ] LaTeX builds without undefined references/citations or material layout
      warnings.
- [ ] Ambiguous date and premature reviewer acknowledgment removed.
- [ ] Artifact has a license, tagged release, permanent DOI, and data statement.
- [ ] OS metadata and accidental build debris removed from the release.
- [ ] Final PDF is reproducibly generated from the committed source.

## Desired final claim

After the above work, the manuscript should be supportable at approximately
this claim level:

> We present a reproducible case study applying bounded TLA+ model checking,
> Lean 4 invariant-preservation proofs, and model-based conformance testing to
> three related matching-engine artifacts. The methods provide different and
> explicitly delimited assurance: exhaustive checking within finite TLA+
> configurations, machine-checked preservation of modeled invariants for the
> Lean reference under stated hypotheses, and tested agreement of projected
> C++ behavior on replayed traces. They do not constitute an end-to-end
> refinement proof of the C++ implementation.

