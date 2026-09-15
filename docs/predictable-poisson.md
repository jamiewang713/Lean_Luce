# Lemma 2.1: full predictable Poisson criterion

Status: **COMPLETE for the recorded statement.**

Target: `Luce.predictable_poisson`, `Luce/Section2PoissonCriterion.lean:25`.
Source: `fixed_points.tex:589-603`, `lem:predictable-poisson` and
`eq:poisson-criterion`; proof at lines 606-659.

The exact interface, natural-language translation, variables, typeclasses,
and representation choices are recorded in
`proposals/Section2PoissonCriterion.md`. The user requested a direct proof
and specified literal open-cover compactness. The final interface has no
Hausdorff, metrizability, second-countability, or Radon assumption.

## Mathematical statement

Let I_(n,k) be adapted zero-one observations, p_(n,k) their conditional
means before observation k, and x_(n,k) deterministic points of a compact
space X, equipped with its Borel sigma algebra. Rows are finite, indexed
by 1,...,n as in the surrounding manuscript. For a finite deterministic
nonnegative measure nu, assume

    A_n = sum_k p_(n,k) delta_(x_(n,k)) -> nu weakly in probability,
    max_k p_(n,k) -> 0 in probability.

Then Xi_n = sum_k I_(n,k) delta_(x_(n,k)) converges in law to the finite
Poisson random measure of intensity nu. The Lean conclusion explicitly
quantifies over every bounded continuous real function of the whole point
measure and proves convergence of its expectation.

Repeated locations and zero intensity are included. No independent draws,
uniform bounds on original expected counts, tightness, or deterministic
caps occur as additional hypotheses.

## Following the LaTeX proof

| Manuscript step | Lean evidence |
| --- | --- |
| Adapted indicators and conditional probabilities | `FiniteAdaptedBernoulli`: only filtration, Bool observations, adaptation are input fields. Real indicators and bounded versions of conditional expectations are derived. |
| Predictable recursive deletion, lines 609-615 | `stoppedMass`, `keepTerm`, `stoppedProbability`, `BernoulliProcess.stop`; exact acceptance test, including both boundary equalities. |
| Likelihood martingale, lines 618-624 | `BernoulliProcess.likelihood_martingale`, `integral_likelihood`. |
| Uniform L2 estimate, lines 630-638 | `integral_likelihood_sq_le`, `stopped_integral_likelihood_sq_le`: E[L_m^2] <= exp(K/(1-delta)). |
| Product approximation, lines 642-647 | `product_poisson_error_of_atom_bound`, capped integral error, `capped_laplace_tendsto_rows`. |
| Remove deletion, lines 649-653 | `uncapped_laplace_tendsto_rows`: delta=1/2, K=nu(X)+2, rare deletion event, equality of finite rows off that event. |
| Extract total and tested predictable convergence | `WeakMeasureConvergesInProbability.integral`, `totalPredictable_tendsto`, `pointMeasure_laplace_tendsto`. |
| Limiting Laplace functional, lines 655-659 | `integral_pointLaplace_finitePoissonLaw` computes the actual Poisson iid law. |
| Full random-measure convergence, last sentence | `count_tightness_rows`, `pointMeasure_law_convergence_of_laplace`, then `predictable_poisson`. |

For the L2 step, the proof first obtains the stronger pointwise bound
0 <= L_m <= exp(K/(1-delta)). Multiplying by L_m and using E[L_m]=1 gives
the displayed L2 conclusion. The single-factor conditional-second-moment
identity is not separately exported as a conditional-expectation theorem.
Its scalar algebra is proved. The main limit proof uses the stronger bound
to control the same likelihood/product comparison.

## Literal compactness and the final spatial step

`FinitePointMeasure X` is a subtype of actual finite measures that are
finite sums of unit Dirac masses. It inherits the weak topology and the
evaluation sigma algebra. No equality between the weak Borel sigma algebra
and evaluation sigma algebra is assumed.

For each N, the set of point measures with total count at most N is a
finite union of continuous images of X^m, m <= N, and hence compact by
literal compactness. Laplace coordinates separate points in the moment
image that induces the weak topology. Stone-Weierstrass on these compact
images approximates all bounded continuous state tests. A countable
compact exhaustion proves their evaluation measurability. Clipping the
approximants gives tail bounds independent of approximation size.

Convergence of expectations extends from Laplace coordinates by linearity:
their products are again coordinates, with test g+h. No inference of
product-of-expectation convergence is used. Count tightness is derived
from the stopped process and vanishing deletion probability.

`WeakMeasureConvergesInProbability` uses actual weak-open neighborhoods.
For these finite arrays, their preimages are proved measurable through
the finite vector of conditional probabilities, even though no ambient
weak-open measurability instance is available for all finite measures.

## Poisson law representation

`finitePoissonLaw nu` is the standard finite-intensity generative definition:
N has the actual mathlib Poisson law with mean nu(X); given N=m, take m iid
points of law nu/nu(X) and sum their Dirac measures. For nu=0 the law is the
point mass at the zero measure. Nonemptiness and positivity needed for the
normalization branch are derived internally from nu != 0.

The construction is proved to be a probability measure and its Laplace
functional is computed directly. The separate equivalence with independent
Poisson counts on disjoint measurable sets is not asserted as another
formalized theorem and is not an external assumption in the proof.

## Pinned mathlib dependencies

- `MeasureTheory.FiniteMeasure.continuous_integral_boundedContinuousFunction`,
  `Mathlib.MeasureTheory.Measure.FiniteMeasure`: integration of a fixed
  bounded continuous real spatial test is continuous for the weak topology.
- `BoundedContinuousFunction.toReal_lintegral_coe_eq_integral`,
  `Mathlib.MeasureTheory.Integral.BoundedContinuousFunction`: the real value
  of the nonnegative test's lintegral equals its real Bochner integral.
- `ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints`,
  `Mathlib.Topology.ContinuousMap.StoneWeierstrass`: on a compact space, a
  separating real subalgebra uniformly approximates continuous real tests.
- `ProbabilityTheory.poissonMeasure`,
  `Mathlib.Probability.Distributions.Poisson.Basic`: Poisson probability
  measure on naturals with NNReal rate, including zero.

No Lean or mathlib version changed: both remain pinned to v4.33.1.

## Verification

Verified on 2026-09-10 with the pinned Lean/mathlib v4.33.1:

```powershell
lake env lean Luce/Section2PoissonCriterion.lean
lake build
lake env lean audit/Section2PoissonCriterion.lean
```

The relevant module check passed. The default project build passed with
3700 jobs, including `Luce.Section2PoissonCriterion`, imported by `Luce/Sections1To7.lean:31`.
There are no remaining errors. Nonblocking deprecation/linter warnings
remain, including the deprecated set-membership simplification name in
the final proof.

The audit prints the full theorem, definitions in its interface, and
important proof dependencies. All 17 axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. The final theorem's exact
report is:

```text
'Luce.predictable_poisson' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

A recursive source scan of the theorem's local dependency chain, together
with the separately proved L2 result, found no `sorry`, `admit`, introduced
`axiom`, `native_decide`, or `by_contra!` in the 24 files. The axiom report
also checks the transitive compiled dependency chain for `sorryAx` and
nonstandard axioms. The implemented signature equals the recorded proposal
after whitespace normalization.

Evidence files:

- `audit/poisson-criterion-module.txt`
- `audit/poisson-criterion-build.txt`
- `audit/Section2PoissonCriterion.lean`
- `audit/poisson-criterion-print.txt`
- `audit/poisson-criterion-axiom-summary.txt`
- `audit/poisson-criterion-dependency-files.txt`
- `audit/poisson-criterion-source-scan.txt`
- `audit/poisson-criterion-statement-lock.txt`

## STATEMENT AUDIT

- Target theorem: `Luce.predictable_poisson` (Lemma 2.1).
- LaTeX source/label: `fixed_points.tex:589-603`, `lem:predictable-poisson`,
  `eq:poisson-criterion`.
- Statement changed: NO; recorded interface unchanged.
- Hypotheses added: NO.
- Hypotheses strengthened: NO.
- Conclusion weakened: NO.
- Quantifiers changed: NO.
- Constant dependencies changed: NO.
- Definitions mathematically changed: NO. New equivalent representations
  are explicitly described above and in the statement record.

## TRUST AUDIT

- New axioms introduced: NO.
- `sorry`/`admit` remaining in dependencies: NO.
- External assumptions used: NO.
- `#print axioms` result: `[propext, Classical.choice, Quot.sound]` only.

## BUILD AUDIT

- Relevant module checked: `Luce/Section2PoissonCriterion.lean` — PASS.
- Module included in project build: YES, `Luce/Sections1To7.lean:31`.
- `lake build` result: PASS, 3700 jobs.
- Remaining errors: NONE.

This completes Lemma 2.1. It does not certify all of Section 2: the separate
Luce-specific compensator proposal remains deferred and unapproved.
