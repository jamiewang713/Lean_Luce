# Frozen Lemma 6.4 contract and assumption audit

Status: the full frozen proposition is now proved by `Luce.Section6.lemma64`, with the separate closed `Luce.Section6.lemma64_contractCheck`. The full build and 650-declaration type/axiom audit passed; only permitted foundational axioms occur. See `docs/section6-lemma64-completion.md` for exact statements, actual output and verification. The separate baseline `audit/section6-lemma64-contract-freeze.json` was created after specification elaboration and before the combined proof. All its 45 files remain unchanged. It does not replace the older Section 6 baseline: that older check still fails on the manuscript, and its historical contents remain unavailable.

## Mathematical source and closed targets

Source: `fixed_points_sampled_profile.tex`, Assumption `ass:simple-power-profile` (currently line 385), and Lemma `lem:sp-domination` (currently line 2141), including the fixed-index estimates in its proof. The kernel definitions H_R,H_L immediately preceding the insertion argument use a freely reduced positive exponential constant. The target is the entire global-domination-and-excursions lemma, not the subsequent CLTs.

`Luce/Section6Lemma64Contract.lean` defines three CLOSED propositions:

- `Luce.Section6.Lemma64Contract.matrix` universally quantifies f, endpoint behaviors, the sampling grid, the entire weight array and the marked-label budget. Its only antecedents are PowerProfile and exact SampledRates. It concludes existence of a single nonnegative matrix for every row, with every listed matrix property.
- `Luce.Section6.Lemma64Contract.cycles` universally quantifies the same model data and every positive cycle length represented by k+1. Its only antecedents are the same two predicates. It concludes the literal maximum-root count bounds and the real-cutoff discarded-count expectation bounds.
- `Luce.Section6.Lemma64Contract.lemma64 := matrix ∧ cycles` is the complete target. It is not defined through any implementation theorem. No section variable, caller-supplied instance, matrix estimate, integrability predicate, intensity condition or proof-input record is present.

The matrix is an existential CONCLUSION, as in the manuscript. The requested constant, cutoff, weighted exponent, exceptional exponent and finite-index cutoffs are outputs. Equalities selecting a power endpoint occur inside the output clauses; they distinguish the two allowed endpoint cases rather than restrict the universally quantified models.

## Complete hypothesis content and type restrictions

| Manuscript input | Exact representation and restrictions |
|---|---|
| Positive continuous f on (0,1) | `f : ℝ → ℝ`; `PowerProfile` contains `ContinuousOn f (Set.Ioo 0 1)` and `∀ x ∈ Set.Ioo 0 1, 0 < f x`. Values outside (0,1) are unrestricted. All sample points lie inside that interval. There is no monotonicity, differentiability, global boundedness or integrability assumption. |
| Right power zero or finite positive limit | `EndpointBehavior` has exactly `finite c` and `power c exponent eta`. No restrictions are hidden in the constructors. `RightBehavior f (.power c beta eta)` is `0<c ∧ 0<beta ∧ 0<eta ∧ PowerExpansion (fun s => f (1-s)) c beta eta`. In the finite case it is `0<c ∧ Tendsto (fun s => f (1-s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds c)`. |
| Left nonintegrable power pole or finite positive limit | `LeftBehavior f (.power c alpha eta)` is `0<c ∧ 1<alpha ∧ 0<eta ∧ PowerExpansion f c (-alpha) eta`. In the finite case it is `0<c ∧ Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds c)`. The lower bound alpha>1 is the manuscript assumption, not a summability hypothesis added for the proof. |
| Relative power expansion | `PowerExpansion g c exponent eta` is the literal `Asymptotics.IsBigO` at zero from the right of `fun s => g s / (c*s^exponent) - 1` against `fun s => s^eta`. No convergence rate constant is a caller input. Each active endpoint stores its error exponent. |
| At least one active endpoint | The last PowerProfile field is `left.active ∨ right.active`. `active (finite _) = False`; `active (power _ _ _) = True`. |
| Exact sampled rates | `WeightArray := (n : ℕ) → Weights n`. `Weights n` has exactly `rate : Fin n → ℝ` and `positive : ∀ i, 0 < rate i`. `SampledRates grid w f` is `∀ n i, (w n).rate i = f (samplePoint grid n i)`. Strict positivity in the weight type is already supplied by the original positive f at its sample points. No normalization field exists. |
| Sampling convention | `SamplingGrid` has midpoint and interior. Midpoint samples are `(i.val+1/2)/n`, exactly the manuscript's `(i-1/2)/n` after converting one-based labels. Interior samples are `(i.val+1)/(n+1)`. The contract proves both grid cases; in particular its midpoint specialization covers the manuscript models. |
| Index domains | `n : ℕ`, labels `Fin n`; original one-based label i is i.val+1. Left depth is i.val+1; right depth is n-i.val. Depths are positive for every label. Including n=0 adds only the empty finite model; no positive-row case is excluded. Cycles have length k+1 with k arbitrary natural, so fixed points are included. |

No normalization or shell condition is assumed in this Section 6 contract. They are not hypotheses of this sampled-profile lemma. No old gamma-dependent endpoint assumption is retained.

## Probability, counts and full conclusions

`exponentialRace w` is `Measure.pi (fun i => expMeasure (w.rate i))`. Its probability-measure instance is proved from the positive rates; it is not an assumed law or independence instance. `raceRank clocks i = 1 + card {j | clocks j < clocks i}`. `MarkedRankCylinder u j clocks` is `∀ a, raceRank clocks (u a) = (j a).val+1`. The contract explicitly requires distinct marked labels and distinct demanded ranks, and allows every number of marks up to r, including zero.

`raceRankPermutation` agrees with the actual rank map on distinct clocks and is extended by the identity on ties; ties have proved probability zero. The cycle objects are the existing `cycleOrbits R k`, genuine orbits modulo rotation of minimal length k+1. `cycleMaximum` is the maximum of the literal finite orbit; injectivity and the exact indicator/count identities are proved elsewhere. The root conclusion uses the CARDINALITY of cycles with that maximum, not an abstract intensity or a caller-supplied count.

`intervalDiscardedCycleCount` filters those same literal cycles by A<=depth(maximum)<=B and existence of an orbit vertex outside [A,B]. Its real-cutoff representation and exact integer-rounding equivalence are proved. It does not replace or change the earlier logarithmic excursion count.

The matrix contract explicitly contains nonnegativity; the joint cylinder product bound; all-n row bounds; all-n middle target maxima and column sums; active endpoint target maxima and columns; both global weighted rows with a positive exponent; same-corner ordinary-plus-exceptional envelopes with their exact left/right orientations; the fixed-left bound C*theta_i/n^alpha; fixed-right source-depth stretched-exponential decay and the corresponding outside-corner decay in n. One C and delta serve the matrix clauses. The ordinary and exceptional kernels use output positive d,nu and 0<v<=1, and the fixed cutoffs H are positive integers. Inactive endpoint clauses impose no mathematical restriction.

The cycle contract contains interior C/n maximum-root expectations, active-corner C/depth maximum-root expectations, and uniform discarded expectations for real A,B whenever B/n<=delta. For n>=1, the latter is precisely B<=delta*n; n=0 has no cycles. Reversed or otherwise empty intervals count zero rather than require a new hypothesis.

## Proof construction and completed obligations

`lemma64_matrix` now proves the complete matrix component; `lemma64_cycles` proves the complete cycle component. `lemma64` combines them and the separate `lemma64_contractCheck` obtains the full frozen proposition from that theorem. No declaration has additional parameters. No contract field was moved to an antecedent and no frozen definition changed. The component descriptions below record their roles in this completed construction; their earlier statements about assembly still being pending are historical.

Current new implementation results remove the large-n premise from the middle maxima/columns and prove the exact fixed-left rate estimate for all n. The latter uses a finite sum over BOTH grids and all labels in the finite small-row range to construct its absorption constant; it introduces no uniform positive rate floor. These help prove the frozen target but do not alone establish it.

`Section6CommonDecay` constructs positive common decay parameters from numerical upper bounds and a final positive cutoff at most one. Its concrete `PowerProfile.domination_matrix_fixed_right_common` proves both fixed-right source-depth and outside-corner row-size bounds with the SAME coefficient and exponent, below the supplied envelope parameters. All actual matrix estimates are discharged by the original profile theorem; the numeric bounds are not extra model assumptions. This removes a compatibility obligation but does not assemble the full matrix contract.

`Section6RightEnvelopeAssembly` now combines the ordinary-plus-exceptional corner envelope and both fixed-right estimates with one C,d,nu and one integer H. It first returns a positive upper cutoff delta0, then allows ANY positive delta<=delta0 before constructing the common decay parameters. This order permits choosing the final intersection with all other endpoint/column cutoffs without assuming an outside bound at the wrong cutoff. `Section6LeftEnvelopeAssembly` combines the exact left corner envelope and fixed-left C*theta_i/n^alpha estimate with one C and integer H. The finite cutoffs are constructed as max(1,ceil(h)); every row size is covered. These remain concrete components, not the full matrix proposition.

`Section6CommonWeightedRows` constructs a common positive kappa from the original profile: half the minimum of the active endpoint exponents, using 1 for an inactive endpoint. The strict left exponent restriction alpha>1 and right restriction beta>0 prove positivity. Its concrete matrix theorem obtains both actual weighted row bounds at this kappa and adds their constants, so neither a weighted-row estimate nor the existence of a compatible exponent is a new input. The conditional clauses for inactive endpoints are vacuous. The full matrix contract still requires combining this result with the endpoint envelopes, target/column estimates, ordinary rows, interior bounds and cylinder domination.

`Section6ActiveMatrixTargets` now constructs one C and delta for target maxima and column sums at BOTH active endpoints, for every row size and all source subsets. `active_matrix_target_columns` derives all estimates from the original profile using endpoint case analysis, intersects their cutoffs, and adds their constants. There is no assumed target or column estimate. This gives the endpoint target/column component in a form ready to intersect with the envelope cutoffs; it does not yet establish the full matrix contract.
