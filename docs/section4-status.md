# Section 4 formalization: complete (2026-09-10)

## Source contract and environment

Source: `fixed_points.tex:821–962`, Section 4, **The last few positions**
(`sec:endpoint`). Its final proof establishes `thm:main-poisson`, stated at
264–278. `main.tex` inputs this source; Section 4 has no further input files.
The mathematical source was not edited.

Final entry points are `Luce.section4_main_poisson` and
`Luce.section4_main_poisson_general` in `Luce/Section4Theorem.lean`.
All dependencies are proved and imported through `Luce/Section4.lean` and
`Luce.lean`, the default build target. There are no remaining Section 4
obligations or conditional premises standing in for missing proofs.

No applicable AGENTS.md was found in the repository or its parent chain.
Existing sources and configuration were untracked at the initial inspection;
they were preserved without resetting or committing unrelated work. Lean is
`leanprover/lean4:v4.33.1`; mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`). No version was changed.
The initial full build passed (3736 jobs); the resumed baseline passed
(3743 jobs). Both had linter warnings, without compilation failures.

## Exact main statement and all assumptions

For every triangular array of positive real weights θ(n,k), k=1,...,n,
and every real function f, assume:

1. For every n>0, (1/n) Σ_k θ(n,k)=1 (`NormalizedWeights w`).
2. f is Lebesgue measurable and pointwise positive on (0,1), and the literal
   step profiles f_n converge to f in L1(0,1) (`ProfileLimit w f`).
3. There exist γ>0, ε₀>0 and n₀ such that for every n≥n₀ and every label k,
   (1−ε₀)n≤k implies θ(n,k)≥γ (`EndpointAssumption w`).

Then ρ(x,x) is Lebesgue integrable on (0,1), and, for the Luce permutation π_n,

    Ξ_n = Σ_{k: π_n(k)=k} δ_{k/n}  ⇒  PRM(ρ(x,x) dx) on [0,1],
    d_TV(Law(# fixed points of π_n), Poisson(λ)) → 0,
    λ = ∫_(0,1) ρ(x,x) dx ≥ 0.

The spatial convergence quantifies over **every bounded continuous real
function of the finite point measure**, using its induced weak topology.
It is full convergence in distribution, not merely a single Laplace test.
The count distance is exactly sup_A |μ(A)−ν(A)| over all subsets of ℕ.

The canonical theorem uses the existing independent exponential-race model.
The `_general` theorem additionally quantifies over arbitrary row types Ω_n,
measurable spaces, probability measures P_n, and measurable permutations π_n,
with their defining Luce law:

    P_n(π_n=σ) = ∏_r θ(n,σ(r)) / Σ_{j≥r} θ(n,σ(j)).

These are the model and probability-space data, not extra asymptotic
assumptions. No cross-row independence, uniform integrability, count moment
bound, global rate bound, continuity of f, or ε₀≤1 is assumed.
Integrability and ∫f=1 follow from the profile and normalization assumptions.

### Representation and statement checks

- `Weights n` has only the rate function and its pointwise strict positivity.
  `WeightArray` is `(n : ℕ) → Weights n`. Row zero is empty and harmless.
- `ProfileLimit` expands to null measurability for restricted Lebesgue measure,
  pointwise positivity on (0,1), and `ProfileL1Convergence`. The latter uses
  the extended L1 seminorm, so infinite errors cannot become default real zeros.
- f is extended to ℝ only to use existing integral APIs; values outside (0,1)
  are unrestricted. All substantive profile integrals exclude the endpoints.
- `profileDiagonal f x` is exactly
  f(x) exp(−f(x)t_x)/D(t_x), with the already proved inverse `profileQuantile`
  for F(t)=1−∫exp(−tf). No new density or quantile was substituted.
- The paper's label k is `Fin n` value k−1; its location is `(k.val+1)/n`.
  `fixedPoints_realMeasure` proves the exact real-line sum of Dirac measures.
  The inverse permutation has the same fixed labels. `fixedPointCount_eq_card`
  proves the literal fixed-label cardinality, including the empty row.
- `FinitePointMeasure` is a subtype of actual finite measures represented by
  finite sums of unit Dirac masses, with the induced weak topology. It is
  not an abstract predicate asserting the desired limit.
- `fullIntensity_projection_recovery` recovers exactly
  `(volume.restrict (Ioc 0 1)).withDensity (ENNReal.ofReal ∘ profileDiagonal f)`.
  Endpoint singleton masses vanish; `integral_fullIntensity` proves the
  real Ioo integral identity. Thus excluding endpoints does not alter λ.
- `fullIntensity_mass` and `section4_lambda_nonneg` show that
  `Real.toNNReal λ` is the exact scalar Poisson parameter; no truncation is
  hidden by this coercion. Zero intensity is allowed.
- `finitePoissonLaw_count_joint` identifies all finite families of disjoint
  measurable-set counts as independent scalar Poisson counts. This checks the
  meaning of PRM, rather than relying on the constructed law's name.
- Fully explicit elaborated types, universe/typeclass parameters, expanded
  definitions and readable theorem types are printed by `audit/Section4.lean`.

## Source-to-Lean coverage and dependency map

Every row below is **fully proved**; remaining obligation: **none**.
File names in the table are under `Luce/` and have extension `.lean`.

| Source label / lines | Lean declarations and files | Reuse / completed work |
| --- | --- | --- |
| `eq:mean-survivors`, 831 | `meanSurvivors` (`Endpoint`), `integral_clockSurvivalIndicator` (`EndpointRace`), `integral_sum_clockSurvivalIndicator` (`Section4Endpoint`) | Existing individual identity; packaged exact sum identity. |
| `lem:rank-integral`, 835–847 | `rank_integral` (`ApprovedRankIntegral`) | Reused the proved conditioning/integrability and arbitrary-law bridges. |
| `eq:two-candidate`, 851–856 | `two_candidate_sum_bound` (`TwoCandidate`), `sum_otherSurvivorProbability_le_two` (`EndpointRace`) | Reused exact deterministic and probability bounds. |
| `prop:endpoint-bound`, `eq:B-definition`, `eq:tail-explicit`, 858–870 | `section4_endpoint_bound` (`Section4Endpoint`); existing `EndpointTheorem`, `EndpointCutoff` | Packaged B=√(nM) and both inequalities with universal c=(1/2−exp(−1))/2. |
| Finite size side conditions, 859–865 | `endpoint_window_le_row_of_size_condition` (`Section4EndpointWitness`) | Proves M≤n from 1≤M and M≤(√(nM)−1)/2. The indexing premise is redundant, not a restriction. The explicit terminal rate premise makes ε₀ unnecessary in the finite lemma. |
| `eq:tail-epsilon`, 872–914 | `section4_tail_expectation_bound`, `tailFixedPointCount_expectation_eq` (`Section4Endpoint`); `section4_tail_expectation_bound_of_endpoint_witness` (`Section4EndpointWitness`) | Transfers existing asymptotic estimates to arbitrary independent exponential-clock row spaces; witness version retains any original admissible γ. |
| `rmk:minimal-tail`, 917–921 | Endpoint theorem signatures | Endpoint estimates require normalization and terminal lower rates only, without a profile assumption. |
| `cor:interior-poisson`, 808–819, used at 924 | `section3_interior_poisson`, `section3_interior_poisson_general` (`Section3Poisson`), predictable-test and maximum theorems | Reused the completed Section 3 architecture and actual model-derived estimates. |
| `eq:tail-tightness`, 930 | `tail_fixed_point_tightness` (`TailTightness`), `fixedPoints_tail_count`, `section4_point_measure_tail_tightness` (`Section4Count`) | Existing probability estimate; exact random-point-measure count bridge proved on the a.e. no-ties event. |
| Truncation/expectation argument, 934–944 | `ConvergesInProbability.le_limsup_integral` (`Section4Fatou`), `integral_predictable_eq_observed`, `section4_interior_test_expectation_lower` (`Section4Compensator`), `section4_intensity_test_bound` (`Section4IntensityEstimate`) | Completed nonnegative truncation, compensator/observation expectation identity, and uniform terminal-test estimate; boundedness premises discharged. |
| `eq:intensity-tail-bound`, 947–952 | `section4_full_intensity_finite`, `section4_profileDiagonal_integrable`, `section4_intensity_tail_tendsto` (`Section4Intensity`) | Proved actual full-density finiteness, integrability, and vanishing terminal integral. |
| Intensity restriction limit, 950–955 | `fullIntensity`, `fullIntensity_mass`, `tendsto_integral_interiorIntensity_full`, `tendsto_laplace_finitePoissonLaw_interior_full` (`Section4FullIntensity`) | Constructed finite full intensity from the proved finiteness and connected interior laws to it. |
| Full `eq:point-process-limit`, 953–956 | `section4_laplace_cutoff_error` (`Section4Approximation`), `pointMeasure_tightness_of_laplace` (`LaplaceCountTightness`), `section4_full_laplace`, `section4_full_poisson`, `section4_full_poisson_general` (`Section4Poisson`) | Proved terminal approximation, count tightness and full weak-law convergence; no conditional estimate remains. |
| Total-count mapping, 956 | `finitePoissonLaw_count_univ`, `pointMeasure_random_count_singleton_poisson_tendsto` (`Section4CountLaw`) | Proved continuity of total count and exact limiting scalar law. |
| Discrete Scheffé step, 958–961 | `tendsto_probabilityTotalVariation_of_singletons`, `_of_weak`, `_of_integrals` (`DiscreteTotalVariation`) | Proved uniform event-probability convergence by a finite-core argument. |
| `eq:count-poisson`, 958–961 | `section4_count_poisson`, `section4_count_poisson_general` (`Section4TotalVariation`) | Applied count-law and TV lemmas; replaced full-intensity mass by the literal λ integral. |
| Entire `thm:main-poisson`, 264–278; proof 923–961 | `section4_main_poisson`, `section4_main_poisson_general` (`Section4Theorem`) | Bundles integrability, full spatial convergence and total-variation convergence under precisely the model assumptions. |

Shortest completed chain:

    existing endpoint/rank/Chernoff estimates → tail tightness
    existing Section 3 compensator convergence → terminal intensity estimates
      → finite full intensity and vanishing intensity tail
    existing interior Laplace limits + the two tail results → full Laplace limit
      → count tightness → existing general point-measure law criterion
      → full spatial law → continuous total-count map → discrete TV convergence.

The generic approximation, tightness and law-transfer lemmas have explicit
hypotheses appropriate to their reusable role. Their applications in the
main Section 4 theorems prove every one of these hypotheses.

## Documented proof-strategy differences

1. The existing asymptotic endpoint proof uses the linear cutoff
   B=√ε·n instead of √(n⌈εn⌉). It retains exactly the source bound
   `2^(1+γ/2) * ε^(γ/4)` for every sufficiently small ε, with δ allowed to
   depend on the array and the specified endpoint witnesses. The new witness
   wrapper retains the original γ rather than merely producing some γ.
2. For intensity finiteness, the proof uses truncation of the already proved
   nonnegative compensator limit in probability and equality of compensator
   and observed expectations. This replaces the paper's truncation/Fatou
   argument on Poisson count limits. No convergence of unbounded means or
   uniform integrability is assumed. Actual eventual expectation boundedness
   is proved before real limsup estimates are used.
3. The full spatial extension is implemented through bounded Laplace tests
   and terminal-event approximation. A bounded Laplace-gap estimate proves
   tightness of total mass, then the existing full weak-law criterion applies.
4. The discrete Scheffé upgrade uses finite-core/tail estimates directly in
   the supremum-over-events distance. Its conclusion and normalization are
   exactly the paper's.

These are proved changes of argument, with no change to the mathematical
claims or assumptions. No mathematical source gap remains unresolved.

## Final proof audit and reproducibility

- Targeted checks of every new module: PASS. In particular,
  `lake env lean Luce/Section4Theorem.lean` passed before the full build.
- `lake build`: PASS, exit 0, **3754 jobs**. The output explicitly includes
  `Luce.Section4Theorem`, `Luce.Section4` and the default `Luce` target.
  Only linter warnings remain, including harmless haveI/letI style suggestions.
- `lake env lean audit/Section4.lean`: PASS, exit 0. All **40** axiom reports
  list exactly `[propext, Classical.choice, Quot.sound]`, including both
  bundled main theorems, canonical/general spatial and TV theorems, endpoint
  results, and reused Section 3 results. See `audit/section4-audit.log` for
  fully explicit statement output and the reports.
- `audit/section4-source-scan.txt`: no admissions, custom axioms,
  `native_decide`, unsafe declarations or proof-checking bypass patterns in
  any production Luce source. Local dependencies from Section 3 and earlier
  sections are included in that scan and in the main theorem's axiom closure.
- No files were excluded from the normal build to hide an unfinished proof.
  Previously completed Section 3 proofs and mathematical sources were preserved.
- Source SHA256, unchanged:
  `0CDC05ACA34BD8E44A949747B815063F969BDD6A4963F650FF1E155B4C6E8E91`.

Audit entry point: `audit/Section4.lean`. Logs:
`audit/section4-full-build.log`, `audit/section4-audit.log`,
`audit/section4-resumed-baseline.log`, `audit/section4-source-scan.txt`.
Earlier incremental audit logs remain historical records; this document
supersedes their former missing-result inventories and approval notes.
