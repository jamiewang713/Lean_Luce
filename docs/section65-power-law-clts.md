# Section 6.5: power-law CLTs and localization

## Completed contracts

`Luce.Section6.powerLaw65` proves `SampledProfileContract.powerLaw grid` and
`Luce.Section6.spatial65` proves `SampledProfileContract.spatial grid`, with the
original universe-polymorphic statements. `Luce.Section6.section65` combines
both results for every supported grid. `Luce/Section65Audit.lean` independently
checks the exact contracts, including explicit midpoint and interior instances,
and is imported through `Luce.Section6`.

The conclusions include coefficient positivity, total and spatial mean
asymptotics, joint Gaussian convergence against every bounded continuous test
function, and expected spatial excursion counts tending to zero. They hold for
every probability-space realization with the stated Luce permutation masses.
There are no added model assumptions, axioms, or weakened conclusions. The
manuscript, frozen definitions, sampling grids, kernels, and toolchain are
unchanged. The critical-pole subsection is separate work; its concurrent
aggregate import has been preserved.

## Proof route

1. **Retain the exact ideal means.** The closed Proposition 6.10 supplies the
   mixed factorial moments of the actual core counts. Falling Pochhammer
   polynomials form a basis, so every fixed polynomial mixed moment follows by
   a finite linear expansion. A polynomial functional specified by
   `L_mu((X)_r) = mu^r` represents the comparison moments. Its proved Stein
   identity yields the centered Poisson moment recurrence; this avoids
   constructing auxiliary Poisson random variables or a coupling.

2. **Control all centering errors.** For the prescribed rounded cutoff
   `A_n = ceil(exp((log n)^(1/4)))`, every fixed logarithmic power times
   `A_n^(-kappa)` tends to zero. The `RapidError65` and `LogGrowth65` helpers
   preserve this statement under the finite sums and products used in
   centering. Lemma 6.8 and coefficient positivity give growth and divergence
   of the exact ideal means. The scaled comparison recurrence converges to
   the actual Gaussian moment recurrence. Consequently all normalized mixed
   moments converge, including mixed corners and different cycle lengths.

3. **Convert moments to the exact weak limit.** Expand each power of a linear
   combination as a finite sum of mixed monomials. A finite Taylor estimate
   for the characteristic function uses an even absolute moment to bound its
   remainder. First take the sample-size limit at fixed Taylor order, then
   send the order to infinity using a Gaussian exponential envelope. No
   exponential-moment assumption on the approximating variables is used.
   Mathlib's finite-dimensional Levy convergence theorem then gives the
   bounded-continuous-test conclusion in the frozen contract. Integrability
   of every actual statistic follows from the finite permutation space.

4. **Replace the mean and remove the core restriction.** Lemma 6.8 gives
   `mu_n = beta * log n + o(sqrt(log n))`; the cutoff correction is negligible
   because `(1 + log A_n) / sqrt(log n)` tends to zero. Exact cycle-set
   comparisons and Lemma 6.7 bound the total omitted count in expectation by
   `O(1 + log A_n)`. This includes roots below `A_n`, roots above the rounded
   `B_n = floor(n/A_n)`, off-active roots, and cycles leaving their core.
   Spatial windows have bounded omission expectation. The characteristic
   function Lipschitz estimate transfers these coordinatewise L1 comparisons
   to the full count limits. The same comparisons transfer the means.

5. **Assemble the total and spatial conclusions.** At each cycle length, sum
   the active-corner Gaussian coordinates with weights
   `sqrt(b_corner / B_total)`. Their squared weights sum to one; the block
   projection therefore has the required independent standard Gaussian
   coordinates. Spatial categories use the original disjoint `Ioc` windows
   and largest-label root throughout. For localization, the actual excursion
   count is bounded by Lemma 6.7 with ratio `n^delta`, giving an expectation
   bounded by `C(1 + log n) n^(-q*delta)`, which tends to zero.

6. **Transfer to arbitrary Luce realizations.** The actual cycle, spatial,
   and excursion statistics are invariant under permutation inversion. The
   exact finite-law identity transfers their integrals from the canonical
   exponential race to the probability spaces in the closed contracts.

## Module map

All new proof modules use the prefix `Luce/Section65`, distinct from the
existing Proposition 6.5 files named `Section6Proposition65...`.

| Part | Principal modules |
| --- | --- |
| Polynomial comparison and rapid errors | `PoissonFunctional`, `CenteredPoisson`, `PolynomialExpansion`, `CorePolynomial`, `RapidError`, `CoreCenteredMoments` |
| Gaussian moments and characteristic convergence | `GaussianMoments`, `PoissonMomentLimit`, `TaylorBound`, `MomentRemainder`, `MomentCharacteristic`, `RaceMomentCLT` |
| Exact means and normalization | `CoefficientPositivity`, `IdealMean`, `MeanAsymptotic`, `CoreScale`, `MeanNormalization`, `CoreTargetMoments` |
| Root and core comparisons | `RootSums`, `CoreCountComparison`, `TotalCoreComparison`, `TotalCoreCutoffs`, `TotalCoreExpectation`, `CountApproximation` |
| Total counts | `ActiveCorners`, `PowerCategories`, `GaussianProjection`, `PowerProjection`, `PowerMean`, `PowerLimit`, `PowerContract` |
| Spatial counts and localization | `LogWindows`, `SpatialCategories`, `SpatialCoreComparison`, `SpatialLimit`, `Localization`, `SpatialContract` |
| Law transfer and closed checks | `InverseCycleStatistics`, `LuceTransfer`, `Section65.lean`, `Section65Audit.lean` |

The complete 51-module list and all 192 named declarations, including 161
theorems, are recorded in `audit/section65-audit-manifest.json`.

## Coverage

The universally quantified proofs cover zero-dimensional vectors (`L = 0` or
`J = 0`), zero moment orders, fixed points, each active corner separately,
mixed active corners, and inactive endpoints. All cutoff conditions are
eventual consequences of the original rounded definitions. The spatial
windows retain their strict left and closed right endpoints, and localization
holds for every positive `delta` and every vertex of the counted cycle.
Small sample sizes require no extra assumptions. Both grids and arbitrary
measurable probability-space realizations are checked by the closed wrappers.

## Verification

New dependencies were compiled sequentially before the aggregate build.
The full project build passed with 4564 jobs after preserving the concurrent
critical-profile import. The dedicated `audit/Section65Closed.lean` prints the
elaborated frozen contract definitions, every new declaration's type, and its
transitive axioms. All 192 declarations passed; the only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The new sources contain no `sorry`,
`admit`, axiom declaration, `unsafe`, or `native_decide`.

The 720-file initial snapshot in `audit/section65-contract-freeze.json` matches
completely, including the manuscript and toolchain. Four older snapshots
retain their pre-existing manuscript mismatches; no historical baseline was
reset. The reproducible validation record is `audit/section65-validation.json`.

The unchanged whole-Section-6 generator produced 1328 successful reports out
of 1337 requested names. Its nine remaining failures are namespace lookups:
five `TraceDensity68` declarations and four `Luce.FiniteAdaptedBernoulli`
declarations. All nine pass the independent
`audit/Section65HistoricalNamespaceSupplement.lean` check with their actual
qualified names and only the permitted axioms. The failed generator run is
retained in `audit/section65-current-audit.log`; the passing supplement is in
`audit/section65-historical-namespace-supplement.log`. The generator is unchanged.
The initial audit snapshot and initial error-limited log are also preserved.
Thus the dedicated Section 6.5 audit passes, while the historical all-source
generator is still reported as failed rather than silently repaired.
