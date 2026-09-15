# Independent audit against the sampled-profile manuscript

Reference: `fixed_points_sampled_profile.tex`, as requested by the user. Review date: 2026-09-14 (America/New_York).

**Section 4 follow-up:** The Lemma 4.3 and Corollary 4.7 coverage gaps identified
in this audit are now closed. See the [formalization and scoped verification
record](section4-exceptional-shells.md). The original findings below describe
the earlier snapshot.

## Verdict

**The five main theorems—1.3, 1.4, 1.6, 1.7, and 1.8—have Lean proofs whose final hypotheses and conclusions match the sampled-profile manuscript. I found no extra model assumption at those theorem boundaries.** The interior-grid extension and the independent-clock tail proposition also have checked proofs.

**This is not a certification that every result or calculation in the manuscript has been formalized.** In particular, I did not find checked statements for the individual slow-label charge (Lemma 4.3), the exceptional-shell refinement (Corollary 4.7), or the full explicit Sukhatme corollary (Corollary 1.9). These are coverage gaps, not hidden assumptions in the five main proofs.

The distinction matters: a helper theorem can legitimately have an estimate as a hypothesis. The main theorem must then prove that estimate from the model assumptions. The closed final statements here provide that check; they do not accept population estimates, moment bounds, tightness, or limit laws as extra inputs.

## What was checked

- All production Lean sources, including nested comments and strings, were scanned for proof placeholders, custom axioms, opaque declarations, unsafe/partial declarations, native evaluation shortcuts, and custom elaboration machinery.
- The default library and the additional production audit module were built with the project's pinned Lean 4.33.1 / mathlib v4.33.1 toolchain.
- A fresh compiler inventory printed the fully elaborated types and axiom dependencies of the production theorem constants, including generated/private auxiliaries.
- An additional audit selected declarations by their **originating module**, rather than just their name prefix, and traversed checked types and bodies through transitive dependencies. This includes definitions and contract namespaces outside `Luce`.
- The main theorem statements were compared manually with the manuscript, and their assumptions, statistics, intensities, probability laws, normalizations, and convergence definitions were inspected.
- Existing standalone audit and proposal files were checked separately. A `def ... : Prop` in a proposal is a statement to prove, not a proof of that statement.

The mechanical checks cover all production code. The manual mathematical comparison concentrates on the public manuscript conclusions, their defining objects, and relevant supporting interfaces; it is not a claim to have independently reconstructed all 2,859 source proofs by hand.

### Verification record

- Production: **840 Lean files**, containing **2,859 source theorem/lemma declarations** and **528 definitions/abbreviations**; 69,856 source lines. Generated declarations are counted separately by the compiler.
- Final default build: **passed, 4,578 jobs**. The separately imported `RankIntegralDependencyAudit` module also builds.
- Existing standalone audit/proposal files: **57 checked; 54 pass and 3 fail** on outdated declaration names, detailed below. No file is omitted from that standalone inventory.
- The fresh existing all-theorem inventory reports **5,112 theorem/axiom constants**, including generated/private auxiliaries, and the axiom union `[propext, Classical.choice, Quot.sound]`.
- Source stability: no production source changed between the recorded hash snapshot and the verification check. The audit tool itself was refined during this review; no production Lean proof or theorem statement was edited.
- The mathlib checkout is clean and its commit, `0df444a360eaa60ab8c11dca51a86af692955474`, matches `lake-manifest.json`.
- Independent logical dependency audit: **passed**. The module-based inventory found **5,902 production declarations**, comprising **5,897 safe logical roots** and **5 generated executable companions**. It includes **5,120 theorem/axiom constants** and traversed **64,089 checked transitive declarations**. The only axioms were `propext`, `Classical.choice`, and `Quot.sound`; no unsafe/partial dependency was reachable from a safe logical root. The 8-theorem difference from the older name-prefix inventory reflects its narrower selection rule.

Evidence files:

- [Final build output](D:/princeton/Research/Lean/Lean_luce/audit/independent-review-build-final.log)
- [Additional module build](D:/princeton/Research/Lean/Lean_luce/audit/independent-review-extra-build.log)
- [Independent compiled declaration/dependency audit](D:/princeton/Research/Lean/Lean_luce/audit/independent-review-compiled.log)
- [Short list of final theorem types and axioms](D:/princeton/Research/Lean/Lean_luce/audit/independent-review-main-statements.txt)
- [Final verification summary](D:/princeton/Research/Lean/Lean_luce/audit/independent-review-verification.json)
- [Fresh full theorem-type and axiom inventory](D:/princeton/Research/Lean/Lean_luce/audit/independent-review-ancillary/audit-AllProvedStatements.log)
- [Reproducible Lean audit](D:/princeton/Research/Lean/Lean_luce/audit/IndependentReview.lean)
- [Source inventory and SHA-256 hashes](D:/princeton/Research/Lean/Lean_luce/audit/independent-review-source-inventory.json)
- [Standalone audit/proposal results](D:/princeton/Research/Lean/Lean_luce/audit/independent-review-ancillary/results.json)
- [Manuscript statement inventory](D:/princeton/Research/Lean/Lean_luce/audit/independent-review-paper-claims.json)

The manuscript inventory's label matches are only navigation aids. Missing label text does not establish a missing proof; the actual declarations and definitions were checked before drawing the coverage conclusions below.

## Main theorem correspondence

| Manuscript result | Checked entry point | Assumption/conclusion assessment |
|---|---|---|
| Theorem 1.3: fixed-point Poisson process and count total variation | [section4_contractCheck](D:/princeton/Research/Lean/Lean_luce/Luce/ShellContractCheck.lean:10), proving [ShellMigrationContract.section4](D:/princeton/Research/Lean/Lean_luce/Luce/ShellMigrationContract.lean:18) | Mean-one normalization, positive measurable L1 profile limit, and the literal shell condition. Includes integrability of the diagonal intensity, the spatial process limit, and total variation of the count. |
| Theorem 1.4: joint short-cycle Poisson limits | [section5_contractCheck](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellContractCheck.lean:4), proving [ShellMigrationContract.section5](D:/princeton/Research/Lean/Lean_luce/Luce/Section5ShellContract.lean:11) | The same finite-mean assumptions. Includes actual cycle counts, integrability/nonnegativity of all trace intensities, independent Poisson coordinates, and joint total variation. |
| Theorem 1.6: power-law joint CLT and means | [powerLaw65](D:/princeton/Research/Lean/Lean_luce/Luce/Section65PowerContract.lean:12), proving [SampledProfileContract.powerLaw](D:/princeton/Research/Lean/Lean_luce/Luce/Section6Contract.lean:11) | Exact sampling and the original continuous positive power profile. Includes coefficient positivity, the stated deterministic centering/scaling, all fixed finite-dimensional joint limits, and mean equivalence. |
| Theorem 1.7: spatial joint CLT and localization | [spatial65](D:/princeton/Research/Lean/Lean_luce/Luce/Section65SpatialContract.lean:12), proving [SampledProfileContract.spatial](D:/princeton/Research/Lean/Lean_luce/Luce/Section6Contract.lean:29) | The same profile/sampling assumptions, with the stated disjoint interior logarithmic windows. Includes means, joint independent normal limits, and expected counts of cycles with an escaping vertex tending to zero. |
| Theorem 1.8: critical pole | [critical](D:/princeton/Research/Lean/Lean_luce/Luce/Section6Critical.lean:17), proving [SampledProfileContract.critical](D:/princeton/Research/Lean/Lean_luce/Luce/Section6Contract.lean:58) | Continuous positive profile, the relative first-order left pole expansion, and a finite positive right limit. Includes the log-log fixed-point CLT, its mean equivalence, and a uniform-in-n mean bound for every fixed longer cycle length. |
| Lemma 6.12: interior-grid extension | [lemma612 and section6](D:/princeton/Research/Lean/Lean_luce/Luce/Section6Lemma612.lean:15) | The three complete power/spatial/critical conclusions hold on both sampling grids. This is a proved conjunction, not merely a definition of the targets. |
| Proposition 7.1: general independent-clock tail | [proposition71](D:/princeton/Research/Lean/Lean_luce/Luce/Section7ContractCheck.lean:15), proving [GeneralClockTailStatement](D:/princeton/Research/Lean/Lean_luce/Luce/Section7Contract.lean) | A universal positive constant precedes all model data. Inputs are independent clocks with probability densities, the stated cutoff equality and numerical condition, and an integrable density envelope. |

## Exact assumptions, including those hidden behind names

### Finite-mean results

[Weights](D:/princeton/Research/Lean/Lean_luce/Luce/Model.lean:22) contains only the finite real rate vector and strict positivity of every rate. It has no uniform rate bound, moment bound, or asymptotic condition.

[NormalizedWeights](D:/princeton/Research/Lean/Lean_luce/Luce/Assumptions.lean:29) is the background mean-one normalization in manuscript equation `eq:normalization`. Although it is a separate Lean argument, it is not an additional assumption introduced by the formalization.

[ProfileLimit](D:/princeton/Research/Lean/Lean_luce/Luce/Assumptions.lean:58) consists of Lebesgue measurability on the open unit interval, pointwise positivity there, and convergence of the literal step profiles in the extended nonnegative L1 seminorm. The manuscript likewise states a positive-valued measurable profile. Integrability and integral one are derived, rather than assumed as extra fields. Using the extended seminorm prevents a divergent real integral from being mistaken for a zero error.

[EndpointShellAssumption](D:/princeton/Research/Lean/Lean_luce/Luce/EndpointShellDefinitions.lean:45) uses the finite minimum on each nonempty logarithmic depth shell, zero contribution from empty shells, and the specified iterated limit of shell tails. The outer cutoff and inner row limit have the correct order. It does not demand uniform terminal positivity or a stronger supremum over all rows.

There are older results using [EndpointAssumption](D:/princeton/Research/Lean/Lean_luce/Luce/Assumptions.lean:73), which requires a fixed positive lower bound near the right endpoint. This is explicitly a stronger special case, corresponding to the manuscript's sufficient condition and uniform-endpoint proposition. **The revised main theorems use EndpointShellAssumption instead.** The implication from the stronger uniform condition to the shell condition is itself proved in [EndpointShellCompatibility](D:/princeton/Research/Lean/Lean_luce/Luce/EndpointShellCompatibility.lean).

### Power-law and critical results

[SampledRates](D:/princeton/Research/Lean/Lean_luce/Luce/Section6ProfileDefinitions.lean:24) is exact evaluation at the midpoint or interior grid. It is not an approximation assumption about an arbitrary triangular array.

[PowerProfile](D:/princeton/Research/Lean/Lean_luce/Luce/Section6ProfileDefinitions.lean:53) requires exactly:

- continuity and positivity on `(0,1)`;
- at the left endpoint, either a finite positive limit or a positive-coefficient pole with exponent greater than one;
- at the right endpoint, either a finite positive limit or a positive-coefficient power zero with positive exponent;
- the stated relative positive-power error at active endpoints;
- at least one active endpoint.

[CriticalProfile](D:/princeton/Research/Lean/Lean_luce/Luce/Section6ProfileDefinitions.lean:58) separately encodes the exponent-one left pole and a finite positive right limit. The relative error is the ordinary Big-O relation as the endpoint distance decreases to zero through positive reals.

Neither final regime takes finite-mean normalization, L1 convergence, a shell hypothesis, differentiability, monotonicity, population asymptotics, insertion estimates, independence of cycle counts, or any CLT as an input.

### Probability-space data

The final main statements quantify arbitrary probability spaces and measurable permutation-valued random variables with the exact Luce mass formula. These are the defining data of a random Luce permutation. There is no independence assumption between different rows and no assumption that the user's realization is already constructed from exponential clocks. The equality of the Luce law with the canonical race law and the transfer of the statistics are proved.

For Proposition 7.1, the explicit measurable nonnegative integrable density with integral one is the usual probability-density representation. Independence and the common envelope are assumptions of that proposition in the manuscript. The proof theorem [general_clock_tail](D:/princeton/Research/Lean/Lean_luce/Luce/Section7Tail.lean:59) only needs envelope integrability on the late-time half-line; its closed statement accepts the manuscript's global integrability assumption.

## Checks against weakened or substituted conclusions

- **Cycles are actual cycles.** [Section5Cycles](D:/princeton/Research/Lean/Lean_luce/Luce/Section5Cycles.lean) counts permutation orbits modulo rotation, includes singleton fixed points, proves the rooted-tuple formula and the `1/ell` multiplicity, and proves invariance under inversion.
- **Spatial roots use the largest label at both corners.** [Section6ContractDefinitions](D:/princeton/Research/Lean/Lean_luce/Luce/Section6ContractDefinitions.lean:55) uses `cycleMaximum`, the actual endpoint distances, and actual cycle vertices in the excursion count. The left root has not been silently changed to the smallest vertex.
- **Constants are literal.** The cyclic density is `rho(source,target)`. The power coefficients use the stated Gamma expressions, the literal increment density, Lebesgue convolution, and the division by cycle length. The limiting Gaussian law is the product of standard normal measures. Coefficient positivity and the needed analytic existence results are proved.
- **Centering is the manuscript's deterministic centering.** The vectors use `B_ell log n`, or `b_(sigma,ell) |I| log n`, and their square roots. The critical theorem uses `log log n`. There is no replacement by the exact finite-n expectation or an unspecified centering sequence.
- **Convergence has its usual strength.** The final weak limits test every bounded continuous function of the whole random vector or point measure. [FinitePointMeasure](D:/princeton/Research/Lean/Lean_luce/Luce/FinitePointMeasure.lean) is an actual finite measure represented by sums of Dirac measures, with the inherited weak topology. Total variation is the supremum of event-probability differences, and the laws in use are probability measures.
- **Integrability is not being assumed away.** The finite-mean main contracts explicitly conclude integrability of the diagonal/cyclic intensities. The normalizing coefficients are proved positive. The finite permutation statistics are measurable and bounded in each row. This addresses the risk posed by Lean's totalized integrals and division operations.
- **Index changes are accounted for.** `Fin n` value `i` represents paper label `i+1`; the cycle index `k` means length `k+1`. The empty row and the few initial logarithm values do not affect the limits.

## Coverage gaps and documentation issues

### 1. Exceptional-shell refinement is not covered by the main shell theorem

[Corollary 4.7](D:/princeton/Research/Lean/Lean_luce/fixed_points_sampled_profile.tex:1145) permits exceptional terminal depths and combines regular-shell costs with individual slow-label charges. The implemented shell predicate takes the minimum over the entire nonempty shell. I did not find the exceptional-depth predicate, its claimed tail estimate, or a final Poisson theorem under that replacement condition.

Therefore the checked Theorem 1.3 should not be cited as a completed formal proof of this corollary. Its different sufficient condition still needs to be encoded and proved to supply the needed tail conclusion.

### 2. Individual slow-label charge has no identified checked counterpart

[Lemma 4.3](D:/princeton/Research/Lean/Lean_luce/fixed_points_sampled_profile.tex:959) uses the sum of the smallest remaining rates in the bound `theta/(theta + A)`. I found the rank-integral and block-capacity proofs, but no checked statement of this individual bound or its smallest-rate-sum object. This omission is relevant to the exceptional-shell corollary; it is not a premise smuggled into either finite-mean main theorem.

### 3. Sukhatme is a specialization still to package and verify explicitly

[Corollary 1.9](D:/princeton/Research/Lean/Lean_luce/fixed_points_sampled_profile.tex:533) has the necessary general foundations: the interior-grid CLTs are proved, and positive scaling preserves the finite Luce masses. Mathematically, `f(x)=1-x` on the interior grid gives the normalized Sukhatme rates, and scaling by `n+1` gives the stated weights.

However, I did not find a checked theorem performing that specialization, identifying all its displayed constants, or proving the Bessel identity/numerical value for `b_2`. The general CLT evidence is strong; the whole displayed corollary should not be described as explicitly formalized yet.

### 4. Historical documentation is not a reliable current inventory

The README still names the older manuscript entry point and contains older completion-status paragraphs. The existing current-statements catalog reports 253 production files, whereas this review found 840. Some Section 6 audit prose still says the main contracts are open even though the current code proves them. This report uses current source and freshly compiled checks rather than treating those historical descriptions as authoritative.

Unnumbered examples, special-function evaluations, alternative sufficient conditions, and general-clock research proposals are not all certified by the five main theorem checks. In particular, defining a candidate bulk density in Section 7 does not prove a microscopic limit for every independent-clock family; the manuscript itself leaves that as a model-specific obligation.

### 5. Three historical audit files do not compile

| File | Fresh result |
|---|---|
| [Section6Current.lean](D:/princeton/Research/Lean/Lean_luce/audit/Section6Current.lean:899) | 18 diagnostics from 9 incorrectly qualified declaration names. |
| [Section6CurrentLemma69Snapshot.lean](D:/princeton/Research/Lean/Lean_luce/audit/Section6CurrentLemma69Snapshot.lean:729) | 10 diagnostics from 5 incorrectly qualified declaration names. |
| [Section6CurrentSection65Before.lean](D:/princeton/Research/Lean/Lean_luce/audit/Section6CurrentSection65Before.lean:783) | 10 diagnostics from the same 5 incorrectly qualified declaration names. |

For example, `Luce.Section6.convolution_bound` should refer to `Luce.Section6.TraceDensity68.convolution_bound`. The four Bernoulli-process identities belong to `Luce.FiniteAdaptedBernoulli`, not `Luce.Section6`. The actual declarations exist; the [namespace supplement](D:/princeton/Research/Lean/Lean_luce/audit/Section65HistoricalNamespaceSupplement.lean) checks their correct names and passes. The diagnostics occur in `#print` / `#print axioms` commands. These files are outside the default library's import chain and their failures do not invalidate the checked main proofs.

Accordingly, “the production library builds” is accurate; “every existing Lean file compiles” is not. The failing historical sources were preserved during this review.

## Meaning of the axiom result

The expected foundational axiom set is `propext`, `Classical.choice`, and `Quot.sound`: propositional extensionality, classical choice, and quotient soundness. These are standard Lean/mathlib foundations, not extra hypotheses about Luce permutations. An assertion of “no axioms at all” would be inaccurate.

The relevant assurance is: no `sorryAx`, no project-specific mathematical axiom, and no undisclosed model hypothesis is needed by the checked main results. The manual statement comparison is what connects those kernel-checked statements to the manuscript's mathematical claims.

Lean can generate unsafe executable companions for safe recursive definitions, such as `convolutionDensity._unsafe_rec`. An initial audit that indiscriminately treated every generated executable declaration as a logical root flagged that companion. Such a flag alone is not an axiom or a proof gap. The final audit inventories these companions separately, starts from every **safe** production definition and theorem, and still rejects any unsafe/partial declaration reached through their logical types or proof bodies. This distinguishes compilation machinery from the dependencies that justify a theorem.

## Recommended scope of a certification claim

It is reasonable to state that the five main limit theorems of the sampled-profile manuscript, their mean/localization assertions, the two-grid extension, and the independent-clock tail proposition have Lean proofs under their stated model assumptions.

It is premature to state that every result and explicit calculation in the entire manuscript has been formalized. The missing items above should be completed or listed explicitly as outside the current formalization.
