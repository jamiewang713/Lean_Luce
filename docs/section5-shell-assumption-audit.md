# Frozen Section 5 shell contract

The mathematical authority is `fixed_points_shell_condition.tex`, `eq:cycle-intensity` and `thm:short-cycles` (lines 335–354), together with normalization, profile convergence, and the raw endpoint shell assumption. The contract is `ShellMigrationContract.section5` in `Luce/Section5ShellContract.lean`. It is a closed proposition defined independently of the implementation. It is now proved by the separate `section5_contractCheck`, without changing the frozen contract or its imported definitions.

## Inputs and restrictions

The complete finite-model, profile, and shell audit is shared with `docs/shell-assumption-audit.md`. Explicitly:

- `WeightArray` is a row for every natural n. Each `Weights n` consists only of real rates indexed by `Fin n` and a proof that each rate is strictly positive. No uniform lower bound, upper bound, or regularity is in this type. Row zero has no labels.
- `NormalizedWeights` asserts mean-one rates separately for every n > 0.
- `ProfileLimit` asserts Lebesgue measurability on (0,1), pointwise positivity there, and L1 convergence of the actual step profiles. It does not assume extra integrability, moment convergence, or uniform integrability. Values outside (0,1) are unrestricted.
- The contract spells out the raw iterated shell limit, using the original `shellCost`: nonempty shells only, real log(n/m), attained finite minimum, n tending to infinity before the shell cutoff. No buffering or tightness result is conjoined.
- `Ω`, its row measurable spaces `mΩ`, and row measures `P` are universally quantified. The sole measure instance is explicitly quantified total mass one. There is no cross-row independence assumption.
- `π` is an arbitrary measurable permutation-valued realization of the exact finite Luce masses. `Equiv.Perm (Fin n)` means all bijections, not a restricted class. Measurability uses the discrete sigma algebra on the finite permutation space.
- L ranges over all naturals. Index k in `Fin L` refers to length k+1. Allowing L=0 just includes the vacuous empty vector.

There are no ambient mathematical section variables, assumed instances, proof-input structures, or existential witnesses in the hypotheses. Universes are polymorphic. Normalization, profile, and the raw shell condition are the only asymptotic premises.

## Exact objects and full conclusion

`Luce.Section5.cycleCount R k` is the cardinality of the set of actual periodic orbits of length k+1, represented by mathlib cycles modulo rotation. Singleton fixed points are retained. `cycleCountVector` simply applies that existing count to each coordinate. The existing `cycleCount_symm` establishes invariance under reversing the permutation; changing between draw and rank permutations does not change the cycle vector.

`cycleTraceIntegrand f k x` is the product of the existing density `cyclicProfileDensity f (x a) (x (finRotate (k+1) a))`. `finRotate` gives the cyclic successor, including the closing edge. The density is the literal rate kernel divided by the limiting survivor denominator, using the existing profile quantile. `cycleTraceIntensity` divides its integral by k+1. There are no bounded-density, inverse-law, or denominator-nonzero assumptions hidden in these definitions.

The product integration measure is the existing `cyclicProfileMeasure`: the product of Lebesgue measure restricted to (0,1). `cyclicProfileMeasure_eq_closed_cube` and `cycleTraceIntensity_eq_manuscript` are the representation obligations identifying this with the manuscript's integral over the closed unit cube, whose boundary has zero Lebesgue measure.

`cycleVectorPoissonLaw` is the product of the existing Poisson measures, with parameters `Real.toNNReal (cycleTraceIntensity f k)`. The contract explicitly concludes integrability of every cyclic integrand and nonnegativity of every raw parameter, so the coercion cannot mask a negative or divergent intensity in a completed proof. Independence is specified by the product law in the conclusion, not assumed of the finite model.

The contract concludes both weak convergence against every bounded continuous real test on the count vector and total variation of the actual pushforward laws. `cycleVectorTotalVariation` is exactly the supremum over all events of the absolute difference of their real probabilities. On the finite-dimensional natural lattice all subsets are measurable. There is no test-dependent assumption, alternative count, or weakened convergence notion.

## Freeze and remaining obligations

The contract and its raw definitions were elaborated before freezing `audit/section5-contract-freeze.json`. That snapshot also covers their existing production dependencies and the unchanged manuscript/toolchain configuration. Proof work may add new modules; it must not weaken these meanings to make the target easier.

The main theorem `Luce.section5_main_general` and required closed `section5_contractCheck` are proved and included in the default build. The fully elaborated output in `audit/section5-final-audit.log` was inspected: the check has only its universe parameter, and the main theorem has exactly the inputs quantified by the frozen contract. All 18 final transitive axiom reports, including both main theorems and checks, contain only the three allowed foundational axioms. The 162/193/1-file snapshots are unchanged. The final implementation ledger records every helper discharge; no required obligation remains an additional antecedent. See `docs/section5-final-report.md` for the exact statements and actual validation output.
