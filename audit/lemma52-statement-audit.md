# Independent statement audit: Lemma 5.2

Auditor: the `reservoir` subagent, independently of the final theorem author.
Source inspected: `fixed_points.tex:996–1076`, together with the standing
normalization/profile/density definitions at 213–248 and ordered-tuple convention
at 974–975. This is a statement audit, not an inference from an axiom report.

## Status

The actual source declarations and definitions in the following modules were
inspected: `Section5GapLaw`, `Section5MarkedGaps`, `Section5DeletedGaps`,
`Section5MarkedGapBridge`, `Section5MarkedSort`, `Section5GapCoefficient`,
`Section5MarkedCoefficientLimit`, `Section5MarkedExpectation`,
`Section5FiniteTaylor`, `Section5GapReservoir`, `Section5Microscopic`,
`Section5MicroscopicSort`, `Section5CyclicAnalytic`, `Section5CyclicReduction`,
`Section5BulkCylinderAll`, and `Section5Lemma52`. The relevant definitions in
`Model` and `Assumptions` were expanded, rather than treating custom predicates
as opaque hypotheses.

The final source declarations `section5_bounded_marked_asymptotic`,
`section5_cyclic_local`, and `section5_lemma52` have been inspected. A direct
compiler invocation of `lake env lean Luce/Section5Lemma52.lean` initially
failed because `Section5MicroscopicSort.olean` had not yet been built; repeating
it after the dependency build succeeded with exit code 0. The independent
command `lake env lean audit/Section5Lemma52StatementCheck.lean` also succeeded with
exit code 0. Its output is `audit/lemma52-statement-types.log`: explicit
arguments, full names and universes are enabled; twelve actual elaborated
theorem types and seven custom definitions are displayed. The actual final
types and expanded definitions were compared to the source, not only read
from their declaration text. No unexpected mathematical binder appeared.

After the all-row correction below, the independent expanded-type command
was rerun successfully (exit code 0), and the new output was inspected.
The actual elaborated `section5_lemma52` and
`ProfileLimit.weighted_bulk_cylinder_all` both contain `∀ n : ℕ` after a
single `∃ K > 0`. No statement-audit item remains pending for Lemma 5.2.
This audit does not claim completion of the other results of Section 5.

## Contract and binder comparison

- `Weights n` contains exactly positive real rates indexed by `Fin n`.
  `WeightArray` is the triangular array; `NormalizedWeights` is mean one for
  every positive row. These are the source's model and standing normalization,
  not additional Section 5 assumptions.
- `ProfileLimit w f` expands to Lebesgue measurability on `(0,1)`, pointwise
  positivity there, and convergence of the extended `L¹` error to zero.
  Integrability/unit integral are proved in the imported profile development.
  Values outside `(0,1)` are unrestricted. The existing project records the
  approved Lebesgue-measurability representation. No endpoint assumption,
  bounded limiting profile, bounded background rates, or positive bulk lower
  rate is added.
- `section5_cyclic_local` has the exposed parameters `w`, `f`, normalization,
  profile convergence, `r : ℕ`, `0 < r`, `α : ℝ`, `α < 1`, arbitrary
  `τ : Equiv.Perm (Fin r)`, and real-valued `g` continuous on the cube. It
  concludes the full sequence limit, not only a subsequence or `n+1` limit.
- The paper's test function defined on the cube is represented by an ambient
  function with `ContinuousOn` on that cube. The proved
  `exists_cyclic_test_extension` supplies such an extension of every continuous
  subtype test. No global continuity, measurability, or sign condition on the
  ambient extension is required. Boundedness on the compact cube is derived.

## Indices, measures, and constants

- A paper label/rank `k` is represented by `Fin n` value `k-1`;
  `raceRank` itself is one-based. Thus the bulk test is
  `(i a).val + 1 ≤ α*n`, exactly membership in `[floor(α*n)]` for positive rows.
  The event is `raceRank E (i a) = (i (τ a)).val + 1`.
- `cyclicProfileDensity f x y` is `f(x)*exp(-f(x)*t_y)/D(t_y)`:
  the first argument is the source label and the second is the target rank.
  The finite kernel uses the actual source rate, not a point sample of `f`.
- The sum is over embeddings `Fin r ↪ Fin n`, hence ordered distinct tuples.
  `sum_embedding_eq_sum_injective` proves the exact correspondence. Sorting
  permutes source and target tuples together and reindexes a product. No
  `r!`, symmetry factor, or cycle-rotation quotient is introduced.
- `cyclicProfileMeasure` is the product of Lebesgue measure restricted to
  `(0,1)`. `cyclicProfileIntegral_eq_volume` proves equality to the literal
  closed-cube Lebesgue integral, accounting for null boundary hyperplanes.
  `integrable_cyclic_density` proves finiteness before using that integral.
- Grid cells have exactly mass `1/n^r`. The exact comparison-array identity
  retains repeated-tuple kernel terms while the probability sum only counts
  injective tuples. These terms are then controlled, not discarded by fiat.

## The microscopic dependencies are discharged

- The deleted family is exactly `univ \\ removed`, compacted by a proved
  bijection with `Fin (univ \\ removed).card`; its rates are unchanged and its
  actual law is proved measure preserving. Counts and rate sums have no
  multiplicities.
- Gap `q` has lower endpoint `T_q` and upper endpoint `T_(q+1)`, with `T_0=0`.
  `orderedRemainingRate` includes the clock at zero-based position `q`.
  The coordinate theorem proves `ξ_q = W_q*(T_(q+1)-T_q)` for the actual clocks.
  Restricting to every complete elimination order gives its actual order mass
  times the full independent Exp(1) product measure. This is a joint measure
  identity, not merely marginal assertions or an assumed noise vector.
- After sorting, the exact arithmetic is `q_a + a.val = (j a).val`.
  Distinct deleted gaps are derived eventually from macroscopic separation;
  the nonterminal gap condition is derived from `α<1`. The initial gap is
  included. Ties and zero/negative clocks are removed only on proved null sets.
- The deleted empirical CDF at the lower endpoint is `q/n`, at the upper
  endpoint `(q+1)/n`; remaining rate is `W_q/n`. All use the **original** row
  size. The difference between lower-endpoint CDF and target one-based `j/n`
  is at most `r/n` and is explicitly handled in the coefficient limit.
- The finite Taylor theorem's temporary lower bound `W_q≥b*n`, bounded marked
  rates, positive row size, and distinct gap requirements are all discharged
  in `section5_sorted_marked_asymptotic`. The reservoir constant is chosen
  before labels/ranks/orders and is uniform over them. Background rates remain
  unbounded. The final bounded marked theorem quantifies over every fixed
  `M≥0`, every separation `ζ>0`, and every error `ε>0` before the eventual row
  threshold and all configurations.
- The weighted expectation passage does not assume coefficients independent
  of gaps. It uses proved actual-gap identities `E Y=1`, `E Y²=2^r`, and the
  Taylor-envelope expectation `2r`. Measurability, integrability, coefficient
  boundedness, and small bad-event probabilities are all supplied. The finite
  Taylor error is `(2r/n)*(M/b)^(r+1)`.
- The explicit microscopic premises of `bounded_marked_asymptotic_of_sorted`
  and `cyclic_local_of_bounded_marked_asymptotic` are auxiliary interfaces.
  `Section5Lemma52` supplies the proved actual-race theorems to both; neither
  premise is present in the final theorem's mathematical assumptions.

## Boundary cases and proof organization

`r=0` is allowed by auxiliary product/gap lemmas and is handled by empty
products and the probability law on the unique empty vector. The main lemma
requires `r≥1` as in the paper. Positive rows are derived before dividing by
`n`; the `n=0` initial term cannot affect the full-sequence limit. For `α≤0`
and `r≥1` the permitted tuple set and half-open integration cube are empty,
and the final closed-cube integral agrees by the proved boundary identity.
`α=0` is therefore covered without assuming `α>0` globally. `α=1` is excluded.

The formal proof retains the paper's reservoir, deleted race, exact gap
factorization, bounded-rate Taylor approximation, high-rate `L¹` truncation,
and grid-to-profile mechanism. Two reorganizations are mathematically
substantive but valid: the separated-grid reduction uses dominated convergence
off the null diagonal instead of a separate numerical `O(ζ)` strip count;
the deterministic profile replacement directly uses a telescoping integrable
product envelope and `L¹` convergence. Both control the same discarded terms
without stronger assumptions. The weighted bound was proved by successive
prescribed-rank hazards using the same memoryless reservoir mechanism.

## Resolved correction to the initial translation

The printed bound at source 1010–1013 does not explicitly say “for all
sufficiently large n”. The initial translation supplied only an eventual
bound, because the source proof uses an eventual reservoir. The audit flagged
that quantifier interpretation. It is now resolved by the proved
`ProfileLimit.weighted_bulk_cylinder_all`, which absorbs all finitely many
early rows into one finite constant. The construction takes a finite sum of
`n^r / ∏ θ_i`; every denominator is proved strictly positive before it is
used. The cases `n=0,r=0` and `n=0,r>0` are handled explicitly. The final
`section5_lemma52` uses this all-row result. This is a correction toward the
literal source statement, with no stronger hypothesis. The dedicated bound
also shows that its constant is independent of the test function and `τ`.

No changed conclusion, hidden mathematical assumption, reversed orientation,
missing normalization factor, or counting mismatch remains in the inspected
chain. Constants depend on the fixed array/profile, as does the source's
reservoir argument; uniformity across all possible profiles is not asserted.
