# Luce permutations in Lean

Lean formalization project for *Fixed Points and Short Cycles of Luce
Permutations: Poisson Limits and Power-Law Endpoint Singularities*.
The manuscript entry point is `main.tex`, which includes `fixed_points.tex`.

## Sampled-profile Lemma 4.3 and Corollary 4.7

The individual slow-label bound and exceptional-shell refinement are in
`Luce.EndpointExceptionalTheorem`, including endpoint expectation limits and
the full Poisson conclusion under the replacement condition. See the
[statement mapping and verification](docs/section4-exceptional-shells.md).

## Earlier shell-condition migration

The revised shell-condition migration follows `fixed_points_shell_condition.tex`.
Both generalized main theorems and their independently frozen closed contract
checks are now proved. The Section 5 result includes literal intensity
integrability and the full joint Poisson limit in weak convergence and total
variation, without additional mathematical assumptions. See the
[final theorem and audit report](docs/section5-final-report.md).

## Section 7 completion

Section 7's independent-clock tail proposition is proved in
`Luce.Section7.proposition71`, with an independently checked closed statement.
The formalization also includes the exact rank integral, the vanishing-tail
consequence, the candidate bulk density, and the common-shape Gamma envelope.
See [the Section 7 proof and verification record](docs/section7-formalization.md).

## Sukhatme corollary

Corollary 1.9 of `fixed_points_sampled_profile.tex` is formalized as
`Luce.Sukhatme.corollary19`: the joint cycle CLT, mean asymptotics, spatial
CLT and localization, scalar fixed-point CLT, and exact constants
`b_1 = exp(-1)` and `b_2 = K_0(2)`. See
[the statement and verification record](docs/sukhatme-corollary.md), including
the scope of the Bessel definition and the unverified decimal approximation.

## Setup

Install [Elan](https://leanprover-community.github.io/get_started.html), then run
these commands from this directory:

```powershell
lake update
lake exe cache get
lake build
```

The project uses Lean **4.33.1** and mathlib **v4.33.1**. Elan selects the Lean
version from `lean-toolchain`. The mathlib release is pinned in `lakefile.toml`,
and `lake-manifest.json` records exact dependency revisions. Keep these files
together in version control. Mathlib's precompiled cache avoids rebuilding the
library locally; `lake update` normally fetches it automatically.

For subsequent work, run:

```powershell
lake build
```

In VS Code, install the **Lean 4** extension (`leanprover.lean4`) and open this
repository folder. Opening a `.lean` file then starts the Lean language server
with this project's toolchain and dependencies.

## Layout

- `Luce.lean`: library entry point; import new formalization modules here.
- `Luce/Basic.lean`: starter module with a checked mathlib example.
- `Luce/TwoCandidate.lean`: deterministic two-candidate counting bound.
- `lakefile.toml`: library and dependency configuration.
- `lean-toolchain`: pinned Lean version.
- `.lake/`: downloaded dependencies and build output, ignored by Git.

## Approved pilot

`Luce/ApprovedRankIntegral.lean` proves `Luce.rank_integral`, the exact approved
statement of `lem:rank-integral` / `eq:rank-integral` in `fixed_points.tex`.
It applies to independent exponential clocks on an arbitrary probability space
and includes a separate proof of integrability, with no additional hypotheses.
The module is imported by the default `Luce` build.

See [the statement lock and audit](docs/rank-integral.md) for the manuscript
correspondence, dependencies, axiom reports, and reproducible checks. Only this
pilot is certified by that audit; the project does not yet certify completion
of Sections 1–4. Other manuscript results require their own statement reviews.

## Assumption definitions

`Luce/Assumptions.lean` defines the positive weight array, normalization, exact
step profiles, Assumption 1.1's positive Lebesgue-measurable L1 limit, and
Assumption 1.2's uniform endpoint condition. The measurability convention was
approved by the user. See [the assumption record](docs/assumptions.md) for the
source correspondence and verification. The unit-integral consequence remains
a separate theorem to formalize.

## Section 2 work

The current focus is Section 2, “Predictable fixed-point probabilities.”
See [the scope and statement proposal](docs/section2-status.md). Existing
stopping and capped likelihood results are available, including the varying-row
module `Luce.PredictablePoisson` in the default build. The full uncapped Poisson
random-measure criterion, Lemma 2.1, is now proved as
`Luce.predictable_poisson` in `Luce.PoissonCriterion`, with literal open-cover
compactness and no extra spatial separation assumptions. See
[the full statement and audit](docs/predictable-poisson.md).

The approved draw-history definition and pre-draw measurability theorem are
complete in `Luce.HistoryPredictability`; see
[the statement and audit](docs/history-predictability.md). The actual Luce
conditional-probability formula is also complete in
`Luce.PredictableProbability`, with the exact approved signature. The proof
derives prefix probabilities from the full product masses; see
[its statement lock and audit](docs/predictable-probability.md).
Lemma 2.1 uses the standard finite Poisson iid construction and concludes
convergence against every bounded continuous function of the whole point
measure. Its exact interface is in
[the statement record](proposals/Section2PoissonCriterion.md).
The random-measure compensator
[proposal](docs/section2-compensator-proposal.md) is deferred and remains
unapproved.

## Earlier project results

The Section 4 formalization is tracked in
[the complete scope and coverage record](docs/section4-status.md).
`Luce.EndpointAsymptotic` is now part of the default build. Its existing proof
and the finite endpoint estimates have been audited; the paper's exact
interfaces and the final point-process/total-variation argument still require
work. The approved tail-tightness theorem is now proved and audited in
`Luce/TailTightness.lean`; see [its statement and audit](docs/tail-tightness.md).

`Luce/TwoCandidate.lean` proves the deterministic bound labeled
`eq:two-candidate` in `fixed_points.tex`. Removing a candidate from a finite
survivor set leaves either its original cardinality or one less, so at most two
distinct indices can have the required survivor count.

- `Luce.two_candidate_bound_finset`: the bound for any finite set of indices.
- `Luce.two_candidate_bound`: the specialization to indices `0, ..., M - 1`.
- `Luce.two_candidate_bound_Icc`: the paper's indexing `1, ..., M`, with required
  count `m - 1`.
- `Luce.two_candidate_sum_bound`: the paper's bound as a sum of indicators.

These statements require no probability assumptions or injectivity of the
candidate map. The approved pilot above separately establishes the exact
rank-integral identity for independent exponential clocks.

Project setup reference: [Lean projects](https://leanprover-community.github.io/install/project.html).
