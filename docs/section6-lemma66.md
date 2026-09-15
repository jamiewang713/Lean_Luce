# Lemma 6.6: integrable density envelope

Source: `fixed_points_sampled_profile.tex`, `lem:sp-density-envelope`,
lines 2473–2484. The formalization uses the single-coordinate replacement
proof accepted by the user, with the explicit universal constant
`K_ell = 3^ell`. The manuscript itself is unchanged.

## Statement and scope

`Luce.Section6.integrable_density_envelope` proves the expected number of
vertices in `S` belonging to cycles of **exactly** length `ell` is at most
`3^ell * ∫ t, h t`. It also proves integrability of that vertex count.
The probability space and the independent real-valued clock laws are arbitrary.

The only mathematical premises are the manuscript's premises:

- The ambient measure is a probability measure and the clocks are independent.
- Clock `i` has its given density, represented by
  `HasLaw (E i) (volume.withDensity (g i)) P`.
- `ell ≥ 1`; `S` is an arbitrary subset of the finite label set.
- The nonnegative envelope `h` is integrable and dominates the densities
  of labels in `S`.

Densities use Lean's nonnegative extended-real type. The envelope is
real-valued. The main theorem allows domination and nonnegativity almost
everywhere, which is stronger than the manuscript's pointwise formulation.
The closed contract uses the pointwise formulation. No exponential laws,
sampled profiles, moment assumptions, no-ties premise, or restriction on
unselected densities is introduced. There is no lower bound on `n` or
cardinality restriction on `S`.

`exactCycleVertexCount` is literally a filtered cardinality using
`minimalPeriod` of `raceRankPermutation`. It counts vertices, without a
rotation factor or division by the cycle length. Lean label `i` represents
manuscript label `i.val + 1`. The existing rank permutation is extended by
the identity on tied backgrounds; these backgrounds have probability zero
under the stated density laws, as proved in the integration argument.

## Proof

1. `Section6SingleReplacement.lean` replaces coordinate `i` of a common
   background `x` by a fixed time `t`. Every successful exact-length cycle
   gives a forward path ending at `i`. Its first label is within one of
   `clockBeforeCount x t`; each subsequent label is within one of the
   original rank of its predecessor. The intermediate sources avoid `i`
   because the cycle has exact length. Encoding these offsets in
   `Fin ell → Fin 3` gives the bound `3^ell` by an injective map. The code
   is decoded forward, under the same background for every root.
2. `Section6CoordinateIntegration.lean` proves single-coordinate integration
   for arbitrary product probability measures. Replacing the selected marginal
   by a dominating measure, and then applying Tonelli, bounds a sum of
   statistics by the common-background bound times the dominating measure's
   total mass. It also proves almost-sure distinctness and avoidance of each
   fixed insertion time for atomless marginals.
3. `Section6DensityEnvelope.lean` takes the dominating measure to be
   `volume.withDensity (ENNReal.ofReal ∘ h)`. Its finite mass is proved to be
   `ENNReal.ofReal (∫ t, h t)`. All domination, atomlessness, measurability,
   and finiteness hypotheses of the intermediate lemmas are discharged.
   Independence transfers the product-law result to the original probability
   space. Boundedness by `S.card` proves integrability of the actual count.
4. `Section6Lemma66.lean` proves `Section6Lemma66Contract.lemma66`. That
   independent closed contract writes the counted cardinality directly and
   selects the constant before the probability space, `n`, clock laws, and `S`.

## Verification

The entry point is `Luce.Section6.lemma66`, imported through `Luce.Section6`
and the default `Luce` library. Reproduce the checks with:

```powershell
lake build
lake env lean audit/Section6Lemma66.lean
```

The audit checks the closed contract, prints the full main theorem type,
and reports transitive axiom dependencies of the proof components and final
theorem. Results are recorded in `audit/section6-lemma66-audit.log` and
`audit/section6-lemma66-build.log`.

Validation on 2026-09-14: the full default build passed (4296 jobs), and all
16 audited theorem declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`. There are no added axioms, `sorry`, `admit`, or unsafe
declarations in the five new proof/contract source files. Source hashes and
the validation summary are in `audit/section6-lemma66-validation.json`.
