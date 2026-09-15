# Lemma 6.7: root and excursion bounds

Source: `fixed_points_sampled_profile.tex`, `lem:sp-root-excursion`,
lines 2579–2625, under Assumption `ass:simple-power-profile` at line 385.
The manuscript is unchanged.

The entry point is `Luce.Section6.lemma67`, with the closed type
`Luce.Section6.Lemma67Contract.lemma67`. It is included in the default
library through `Luce.Section6Lemma67Totals` and `Luce.Section6`.

## Statement correspondence

| Manuscript requirement | Formal result |
| --- | --- |
| Actual unrooted cycles, rooted at their largest label | `selectedRootCycleCount` uses the existing `Section5.cycleOrbits` and `Section5.cycleMaximum`; `selected_root_singleton67` identifies a prescribed-root count with its indicator. |
| Active-corner root bound `C_L/m` | First clause of `Lemma67Contract.endpointEstimates`, uniformly for every `k < L` and both active corners. |
| Middle and inactive-endpoint contribution bounded uniformly in `n` | `lemma67_regular`, using `offActiveLabels`; there is no exclusion at an inactive endpoint. |
| Roots in `[A,B]`, with a vertex outside `[A,B]`, have bounded expected count | Second clause of `endpointEstimates`, using the unchanged `intervalDiscardedCycleCount`. |
| Logarithmic excursion bound `C_L (1 + log(B/A)) R^(-kappa_L)` | Third clause of `endpointEstimates`, using `logarithmicExcursionCount` with the literal non-strict threshold `log R ≤ abs(log d(v) - log d(root))`. |
| Uniformity up to a fixed length `L` | One positive constant, neighborhood, and exponent are selected before `k < L`, the corner, grid, sampled weight array, and `n`. |
| Counts over all lengths `1,...,L` | `lemma67_excursion_totals` and `lemma67_regular_totals` bound expectations of literal sums of the counts, with constants enlarged by a factor `L+1`. |

Lean index `k` denotes length `k+1`; `k < L` therefore covers precisely
the positive lengths at most `L`, including fixed points. Label `i : Fin n`
represents manuscript label `i.val+1`, and right depth is `n-i.val`.
`A`, `B`, and `R` are real numbers. The hypotheses are `1 ≤ A ≤ B`,
`B/n ≤ delta`, and `1 ≤ R`. Root depths need only satisfy `m/n ≤ delta`;
there is no lower-depth or large-`n` restriction.

For the regular contribution, `offActiveLabels` requires
`eps ≤ (i.val+1)/n` only when the left endpoint is active, and
`eps ≤ (n-i.val)/n` only when the right endpoint is active.
Every fixed middle interval is contained in such a set. A sufficiently
small fixed neighborhood of an inactive endpoint is also contained in
one. Its bound is proved for every `0 < eps < 1` and is uniform in `n`.

## Assumptions and counting fidelity

The only model premises in the closed contract are the unchanged
`PowerProfile` and `SampledRates`. The former is the manuscript's positive
continuous profile with its specified finite or power endpoint behavior;
the latter is exact sampling. Both existing sampling grids are covered,
so midpoint sampling gives the manuscript directly.

No matrix estimate, integrability, concentration, rate bound, independence
condition beyond the existing canonical exponential race, or asymptotic
conclusion is an additional premise of the final theorem. All constants
and cutoffs are constructed outputs. Generic intermediate estimates have
their premises discharged by the original profile and sampling inputs.
No model, probability law, original assumption, or existing count definition
was changed. New counts filter the actual cycles modulo rotation.

Every count is an integrable statistic of the finite race permutation.
`filtered_cycle_expectation_eq_probability_sum` supplies the exact
expectation-to-root-probability identity. `sum_cycle_expectations67` uses
`integrable_race_permutation_statistic` to justify summing expectations.

## Proof

1. Reuse the established active-root and interval-discard bounds.
2. For selected rates in `[d,M]`, specialize Lemma 6.6 to the integrable
   exponential density envelope `(M/d) * exponentialPDF(d)` of mass `M/d`.
   Distinct largest roots inject into selected vertices in cycles of the
   same length. Profile bounds away from active endpoints supply `d,M`.
   The sampling inequalities transfer normalized label cutoffs to sample
   positions using `eps/2`.
3. The existing strict excursion probabilities imply the non-strict
   logarithmic probabilities. For `1 ≤ R ≤ 2`, the ordinary root bound
   absorbs the factor `R^(-q)` with a factor `2^q`. For `R > 2`, a right
   logarithmic excursion reaches depth at least `Rm`, hence strictly more
   than `Rm/2`; on the left it reaches depth at most `m/R`, hence strictly
   less than `2m/R`. Existing weighted path estimates give the required
   decay, with the same harmless factor `2^q`.
4. Sum over the injectively indexed integer root depths. The proved real
   cutoff harmonic bound is `sum 1/m ≤ 1 + log(B/A)`; ceiling and floor
   conversion preserves the stated ratio, including empty intervals.
5. A finite-family argument chooses a common positive constant, smaller
   neighborhood, and smaller positive exponent across both corners and
   all lengths up to `L`. Summing lengths yields the total-count versions.

The proof handles the manuscript's boundary case `R=1` literally: even a
singleton has logarithmic distance zero from its root, so the non-strict
event need not be empty. The ordinary root bound handles it. No change to
the lemma's statement is required.

## Verification

Reproduce with:

```powershell
lake build
lake env lean audit/Section6Lemma67.lean
```

The full default build passed with 4305 jobs. The dedicated audit prints
the closed contract, count definitions, final theorem types, and transitive
axiom dependencies of all 26 new theorem declarations. It also rejects any
transitive axiom of the main theorem or total-count results other than
`propext`, `Classical.choice`, and `Quot.sound` as a Lean error.
The logs and source hashes are saved under `audit/section6-lemma67-*`.

This result does not assert Proposition 6.5 or any subsequent CLT.
