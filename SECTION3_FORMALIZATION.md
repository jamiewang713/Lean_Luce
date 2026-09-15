# Section 3: source contract and verification record

## Authority and environment

The authority is `fixed_points.tex` in this directory, Section 3, **The interior
compensator**, lines 662–819. `main.tex:3` inputs this file. The manuscript is
self-contained: its macros are at lines 21–32; it has no further input/include
dependencies. `commands.tex` and the alternative manuscripts are not inputs.
Mathematical source files must remain unchanged.

Initial SHA256 of `fixed_points.tex`:
`0CDC05ACA34BD8E44A949747B815063F969BDD6A4963F650FF1E155B4C6E8E91`.
No applicable AGENTS.md was found in the project, its parent chain, or its
nondependency subdirectories. Existing untracked Lean work is preserved.

Pinned environment, verified on 2026-09-10:

- Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`).
- Existing `lakefile.toml`, `lean-toolchain`, and manifest are retained.

## Mathematical contract (written before new proof implementation)

Standing data: positive triangular weights θ[n,i], 1 ≤ i ≤ n
(`fixed_points.tex:138–162`), normalized by n⁻¹Σᵢθ[n,i]=1
(213–220). Independent exponential clocks of these rates generate ranks and
the Luce draw permutation. Independence is within each row; no relationship
between different rows is assumed.

Assumption 1.1 (223–229) supplies a Lebesgue-measurable, pointwise positive
f on (0,1) with ||fₙ−f||₁→0, where fₙ=θ[n,i] on ((i−1)/n,i/n].
Integrability and ∫f=1 are consequences, not added assumptions.
H(t)=∫₀¹exp(−tf), F(t)=1−H(t), D(t)=∫₀¹f exp(−tf), t≥0
(236–243); tₓ=F⁻¹(x) for 0<x<1; ρ(x,y)=f(x)exp(−f(x)tᵧ)/D(tᵧ)
(245–248). Set t₀=0 for the compact-interval arguments. Values of f or ρ at
isolated endpoints do not affect the integrals. Endpoint Assumption 1.2 is
NOT a hypothesis of Section 3.

### Lemma 3.1 (`lem:race-law`, 687–705)

For every finite T≥0, sup[0,T]|F̂ₙ−F|→0 and sup[0,T]|D̂ₙ−D|→0 in
probability. For every α<1, max[1≤k≤αn]|τ[n,k]−t[k/n]|→0 and
max[1≤k≤αn]|W[n,k]/n−D(t[k/n])|→0 in probability.
The empirical definitions (670–684) use **≤** for arrival and **≥** for
survival. In particular, W at an arrival includes the arriving label.

### Proposition 3.2 (`prop:interior-compensator`, 735–748)

Under the same assumptions, for every α<1 and every continuous real-valued
g on [0,α], Σ[k≤αn]g(k/n)p[n,k]→∫₀ᵅg(x)ρ(x,x)dx in probability, and
max[k≤αn]p[n,k]→0 in probability. No sign condition on g is permitted.
p[n,k]=θ[n,k]1{R[n,k]≥k}/W[n,k] is the actual conditional probability
(569–578), not a newly assumed process.

### Corollary 3.3 (`cor:interior-poisson`, 808–819)

For every α<1, Ξₙ restricted to [0,α] converges in law to PRM with intensity
ρ(x,x)1[0,α](x)dx. Assumption 1.1 and the normalized model remain standing
assumptions although they are not repeated in the corollary. The external
paper dependency is Lemma 2.1, lines 589–659 (predictable Poisson criterion).

### Range and representation conventions

The substantive interval case is 0≤α<1. For α<0, [0,α] and the selected
labels are empty, so both measures and sums are zero; the integral is over
the empty set, not an oriented integral. α=0 has no selected positive labels
and zero Lebesgue intensity. A supremum of absolute errors over an empty
set is represented by an existential bad event (which is false). Thus no
nonempty-index hypothesis is needed. T<0 also gives an empty time domain.

Lean uses `Fin n` value i for paper label i+1. To avoid the irrelevant empty
row, sequence formulas below can use N=n+1; a shift by one does not change
any limit. The canonical product probability space `Fin N → ℝ` with
`exponentialRace (w N)` represents exactly the independent clocks. Recovery
on any other space with this joint law requires the measurable-law transfer;
it must not be silently asserted if it has not been proved.

## Source-to-Lean dictionary and proposed final types

- weights: `w : Luce.WeightArray`; `Weights.rate`, `Weights.positive`.
- normalization: `Luce.NormalizedWeights w` (expanded above).
- profile: `f : ℝ → ℝ`, `Luce.ProfileLimit w f`, which is exactly
  `NullMeasurable f profileMeasure ∧ (∀ x ∈ Ioo 0 1, 0 < f x) ∧
   Tendsto (fun n => eLpNorm (fun x => stepProfile w n x - f x) 1
     profileMeasure) atTop (𝓝 0)`.
- base measure: `profileMeasure = volume.restrict (Ioo 0 1)`.
- transforms: `profileF profileMeasure f`, `profileD profileMeasure f`.
- F̂: `empiricalArrival`; D̂: `empiricalRemainingGe` (the strict variant
  `empiricalRemaining` can only be used through a proved correspondence).
- Fₙ,Dₙ: `meanArrival`, `meanRemaining`; their equality to profile integrals
  is a required finite-cell computation, not an assumption.
- τ: increasing order statistic of clocks; existing `arrivalTime` on distinct
  clocks must be extended on ties or placed in an a.e. event, with distinctness
  proved from the actual clock law.
- W,p: `Weights.total (remaining π k)`, `predictableChance w π k`.
- Ξ: literal Dirac sum at (k.val+1)/N of fixed-point indicators, represented
  by `observedPointMeasure`/`FinitePointMeasure` and a proved sum identity.
- convergence in probability: for all ε>0, probability of the indicated
  absolute-error bad event tends to zero. Outer measure on existential events
  is allowed and is stronger than an unverified measurability shortcut.

The proposed fully exposed race type is:

```lean
theorem section3_uniform_race
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (T : ℝ) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n+1))
      {c | ∃ t ∈ Set.Icc 0 T,
        ε ≤ |empiricalArrival c t - profileF profileMeasure f t|})
      atTop (𝓝 0)) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => exponentialRace (w (n+1))
      {c | ∃ t ∈ Set.Icc 0 T,
        ε ≤ |empiricalRemainingGe (w (n+1)) c t -
          profileD profileMeasure f t|}) atTop (𝓝 0))
```

The remaining target signatures are mathematical Lean-style specifications;
names `quantile`, `orderTime`, `bulkSum`, `bulkIntensity`, and `bulkPointLaw`
below denote the literal objects just described, not assumed theorem fields:

```lean
-- Every displayed binder must be explicit in the eventual theorem.
-- For all w f hnorm hf α with α < 1:
∀ ε > 0, Tendsto (fun n => exponentialRace (w (n+1))
  {c | ∃ k : Fin (n+1), (k.val+1 : ℝ)/(n+1) ≤ α ∧
    ε ≤ |orderTime c k - quantile f ((k.val+1 : ℝ)/(n+1))|})
  atTop (𝓝 0)
-- And the same statement for |W(c,k)/(n+1)-D(t[k/(n+1)])|.

-- For all w f hnorm hf α (hα : α < 1)
-- and g : Set.Icc (0:ℝ) α → ℝ with Continuous g:
ConvergesInProbability (fun n => exponentialRace (w (n+1)))
  (fun n c => bulkSum w α g n c)
  (∫ x in Set.Icc (0:ℝ) α, g(x) * ρ(x,x))
-- g(x) here means evaluation through the interval subtype, or a proved
-- continuous extension; no extension hypothesis may be added.
-- Plus the zero limit of the maximum actual p, via existential bad events.

-- For all w f hnorm hf α (hα : α < 1):
Tendsto (bulkPointLaw w α) atTop (𝓝 (finitePoissonLaw (bulkIntensity f α)))
```

These last templates are not declarations in a Lean source file. A completed
statement must instantiate all objects and pass a separate statement audit.

## Proof dependency map and planned substantive lemmas

1. Lines 708–713: prove finite-cell integrals, actual profile integrability,
   and real L1 error convergence, then absolute continuity of the integral on
   shrinking cells. Planned `ProfileLimit.max_weight_div_tendsto_zero` assumes
   only `hf : ProfileLimit w f` and proves
   `Tendsto (fun n => rowMax (w (n+1))/(n+1)) atTop (𝓝 0)`.
2. Lines 715–718: use existing globally Lipschitz rate-kernel estimates in
   `Luce.Profile`, plus proved finite-cell identities, to establish convergence
   of the actual means. Do not assume mean convergence as a final hypothesis.
3. Lines 718–726: existing `EmpiricalRace` gives genuine independent-clock
   variance bounds and `RaceConvergence` gives finite-grid interpolation.
   Chebyshev instead of Hoeffding for F̂ is an equivalent concentration step;
   the proof still follows the paper's fixed-time/finite-grid mechanism.
4. Lines 728–732: strict increase and inverse continuity of F, uniform
   quantile inversion including x=0, then random-time substitution for D.
5. Lines 751–758 and 799–805: quantitative denominator replacement and
   maximum bound, with positive lower bound derived from D and α.
6. Lines 759–774: random survival replacement. Planned auxiliary lemmas in
   `Section3Compensator` bound the difference of the two survival indicators
   by `1{|E-t|≤δ}` when `|τ-t|≤δ`; bound
   `r * (expMeasure r).real {E | |E-t|≤δ} ≤ 8*δ/u^2`
   for `r>0`, `δ≥0`, `u>0`, `u≤t-δ`; integrate the finite weighted sum on
   the actual independent-clock law. u>0 is used only after the initial
   label block is removed; it is not a new final hypothesis.
7. Lines 776–797: independence/variance for deterministic survival times;
   step-integral convergence on [η,α]; remove the initial block using L1
   absolute continuity. Do not impose continuity or boundedness on f.
8. Lines 816–818: assemble actual predictable process, Proposition 3.2, and
   Lemma 2.1, including finite intensity and law convergence of point measures.

### Additional implementation specifications (before their implementation)

The deterministic expectation step may be factored into the following general
lemma with explicitly stronger *auxiliary* hypotheses, which are to be
discharged for `c(x)=g(x)/D(t_x)` and `t(x)=t_x`:

```
hf : ProfileLimit w f, 0 ≤ α, α < 1,
ContinuousOn c (Icc 0 α), ContinuousOn t (Icc 0 α),
(∀ x ∈ Icc 0 α, 0 ≤ t x)
⊢ (1/N) Σ_{i : Fin N, (i.val+1)/N ≤ α}
    c((i.val+1)/N) rateKernel (t((i.val+1)/N)) ((w N).rate i)
  → ∫ x in Ioc 0 α, c x * rateKernel (t x) (f x) dx.
```

Dominated convergence for the limiting profile after an L1 comparison is
allowed as an equivalent version of the source's explicit η-cutoff argument
in this deterministic step. It must still prove exact cell enumeration,
the fractional final cell limit, and a dominating integrable function.
No continuity or boundedness of f is introduced.

The stochastic replacement is first proved on a fixed positive time cutoff
u. Its inputs expose `t[k] ≥ u > 0`, bounded deterministic coefficients, and
uniform convergence in probability of the random times to those deterministic
times; its conclusion is a vanishing normalized weighted survival difference.
These inputs are auxiliary only. Applying it to the full proposition requires
removing the initial label block using the original L1 assumption.

The independent-clock/model correspondence (138–162), required before using
Section 2's conditional-probability theorem, is specified as:

```lean
theorem exponentialRace_order_probability {n : ℕ} (w : Weights n)
    (π : Equiv.Perm (Fin n)) :
    (exponentialRace w).real {clocks | StrictMono (fun r => clocks (π r))}
      = w.mass π
```

The planned proof uses induction on the first clock, product exponential
memorylessness, and integration of its density; a proved coordinate
permutation gives arbitrary draw order. The equivalent `raceDraw=π` event
must be related a.e. using distinctness. This result is required, not assumed.

The finite-Poisson construction's correspondence to a Poisson random measure
is to be proved through counts, with this proposed interface:

```lean
-- X is any measurable space; FinitePointMeasure.count must be proved to be
-- the actual natural-valued mass of its measurable argument.
theorem finitePoissonLaw_count_joint (ν : FiniteMeasure X)
    (m : ℕ) (A : Fin m → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    (finitePoissonLaw ν).map (fun ξ i => ξ.count (A i)) =
      Measure.pi (fun i => poissonMeasure (ν (A i)))
```

The planned proof computes the joint Laplace transform and proves uniqueness
on the actual discrete count vectors. Empty families and zero intensities
are retained. A definition packaging this desired equality would not count
as its proof.

## Completed statements and source correspondence

All three results in Section 3 are proved. There are no unresolved mathematical
dependencies, admitted proofs, additional mathematical axioms, or unfinished
theorem interfaces in the Section 3 formalization. The checked entry point is
`Luce/Section3.lean`, imported by the default `Luce.lean` target.

| Source result | Main checked declarations | Conclusion |
|---|---|---|
| Lemma 3.1, 687–705 | `section3_uniform_race_general`, `section3_order_statistics_general`, `section3_uniform_remaining_weight_general` | Both empirical-process limits, uniform quantile limit, and the limit for the actual remaining weight W/n |
| Proposition 3.2, 735–748 | `section3_weighted_compensator_luce`, `section3_max_probability_luce` | The signed weighted compensator integral and vanishing maximum, for any random permutation with the defining Luce law |
| Corollary 3.3, 808–819 | `section3_interior_poisson_general` | Every bounded continuous function of the actual interior finite point measure has the asserted limiting expectation |
| Meaning of PRM in Corollary 3.3 | `finitePoissonLaw_count_joint` | Joint count law on every finite family of disjoint measurable sets is the product of the corresponding Poisson laws |

All names above are in namespace `Luce`. The exponential-space versions remain
available as well. The general versions use the manuscript's original row n,
not merely a shifted subsequence. No coupling of different rows is required.

The main Proposition 3.2 type is literally:

```lean
theorem section3_weighted_compensator_luce
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)),
      (P n).real {ω | π n ω = σ} = (w n).mass σ)
    {α : ℝ} (hα : α < 1) (g : Icc (0 : ℝ) α → ℝ) (hg : Continuous g) :
    ConvergesInProbability P
      (fun n ω => luceInteriorCompensatorSum (w n)
        (intervalTestExtension α g) α (π n ω))
      (∫ x in Ioc (0 : ℝ) α, intervalTestExtension α g x * profileDiagonal f x)
```

`section3_max_probability_luce` has exactly the same binders through `hα`,
with no g or hg, and concludes:

```lean
∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
  {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
    ε ≤ predictableChance (w n) (π n ω) k}) atTop (𝓝 0)
```

The main Corollary 3.3 type is literally:

```lean
theorem section3_interior_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)),
      (P n).real {ω | π n ω = σ} = (w n).mass σ)
    {α : ℝ} (hα : α < 1) (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (interiorFixedPoints α (π n ω)) ∂P n) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (interiorIntensity w f hf α hα)))
```

For Lemma 3.1, the common fully exposed premises are:

```lean
(Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
(P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
(w : WeightArray) (f : ℝ → ℝ)
(hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
(E : ∀ n, Fin n → Ω n → ℝ)
(hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
(hIndependent : ∀ n, iIndepFun (E n) (P n))
```

`section3_uniform_race_general` then takes `(T : ℝ)` and concludes the two
uniform bad-event limits displayed earlier, with `P n`, `Fin n`, and the
clock vector `fun i => E n i ω`. `section3_order_statistics_general` instead
takes `{α : ℝ} (hα : α < 1)` and gives both the quantile and random-time
empirical denominator limits. `section3_uniform_remaining_weight_general`
has these same premises and concludes the literal W statement:

```lean
∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
  {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
    ε ≤ |(w n).total (remaining (raceDraw (fun i => E n i ω)) k) / n -
      profileD profileMeasure f
        (profileQuantile profileMeasure f (((k.val : ℝ) + 1) / n))|})
  atTop (𝓝 0)
```

The complete compiler-elaborated versions, including all implicit universe,
measurable-space, topology, and typeclass arguments, are saved in
`audit/section3-audit.log`. The log is produced by `#check @...` with
`pp.explicit true`, not by manually reconstructing these types.

The source and root-entry-point coverage check found **26 Section 3 source
modules**, **75 local modules** in their transitive import closure, and
**zero Section 3 files outside the checked build**.

## Implemented dependency map

| Proof step and source | Implemented modules and substantive facts |
|---|---|
| Actual profile cells; 213–229, 708–718 | `Section3Profile`, `Section3Mean`: cell disjointness/coverage, exact cell mass and integrals, derived integrability, L1 error convergence, max weight/n → 0, exact mean transforms |
| Uniform race; 715–726 | `Section3Race` discharges all hypotheses of existing `EmpiricalRace` and `RaceConvergence`; fixed-time variance, finite grid, monotonicity, and finite union bound |
| Inversion; 728–732 | `Section3Quantile`, `Section3OrderStats`: F(0)=0, F strictly increasing and tending to 1, positive D, actual inverse identities, continuous inverse including 0, uniform quantile and random-time substitution |
| Actual remaining sets; 681–684 | `Section3Probability`, `Section3RemainingWeight`: bijective rank/draw correspondence and W/n = weak empirical survival at the arrival |
| First approximation; 751–758 | `Section3DenominatorReplacement`: derived positive lower bound, quantitative signed error bound, normalized surviving mass ≤ 1, vanishing error |
| Initial block; 759–774, 779–780 | `Section3InitialBlock`: shrinking initial mass from absolute continuity and L1 convergence |
| Shrinking survival bands; 761–774 | `Section3Compensator`, `Section3Replacement`, `Section3Survival`: actual exponential probabilities, band estimates, expectation/Markov estimates, random→deterministic survival and removal of the initial block |
| Independent fluctuation; 776–780 | Same modules: finite independent variance calculation, positive-time kernel bound, initial-block removal |
| Deterministic expectation; 781–797 | `Section3Expectation`: exact ceil-grid step integral, fractional boundary cell, L1 kernel comparison, proved domination and limiting integral |
| Assembly and maximum; 735–806 | `Section3CompensatorLimit`, `Section3Probability`, `Section3LuceCompensator`: all approximations discharged, continuous signed g on the exact source domain, arbitrary Luce-law model |
| Model and conditional law; 138–162, 569–578 | `Section3RaceLaw`, `Section3RaceDrawLaw`, `Section3LuceLaw`, `Section3Bernoulli`: full permutation mass via exponential memorylessness/induction, measurable ordering, ties null, arbitrary-model law transfer, actual adapted observations and conditional ratio |
| Intensity and literal representations; 245–248, 808–813 | `Section3Intensity`, `Section3Representations`: nonnegative integrable density, finite intensity, exact projection recovery, real-line Dirac sum, closed/open endpoint equality |
| Predictable Poisson conclusion; 816–818 | `Section3PoissonCriterion`, `Section3Poisson`: continuous compensator tests and maximum from Proposition 3.2, checked likelihood argument, count tightness, full law convergence |
| PRM interpretation | `Section3PoissonLaw`: count equals actual mass, joint transforms, proved discrete transform uniqueness, independent Poisson counts on all disjoint measurable sets |

No literature theorem is left as an unproved interface. The Section 2
predictable criterion is supported by the existing local checked likelihood,
stopping, tightness, and compact-approximation proofs. Mathlib supplies, among
other standard results, exponential and Poisson measures, measure-theoretic
integration, independence, dominated convergence, and Stone–Weierstrass.

## Separate statement audit

The actual elaborated types and the definitions printed by the audit were
compared against the source independently of the axiom audit.

| Binder or custom object | Meaning and audit finding |
|---|---|
| Ω, measurable instances, P, `IsProbabilityMeasure` | Arbitrary row probability spaces; represent the source's random variables. No cross-row independence or common-space assumption. |
| `w : WeightArray` | `∀ n, Weights n`; `Weights` contains only the rate function and strict positivity of each source weight. Fin n changes labels, not cardinalities. |
| `NormalizedWeights w` | Exactly mean-one normalization for every n > 0, from source 213–220. Not a new profile hypothesis. |
| `f`, `ProfileLimit w f` | Exactly Lebesgue measurability on (0,1), pointwise positivity there, genuine extended L1 error → 0. Integrability, unit mass, bounded normalized maximum, continuity of transforms and positivity of D are proved consequences. |
| E, `hLaw`, `hIndependent` | The source's independent exponential race. Independence is only within each row. The final Proposition/Corollary also have versions requiring only the defining Luce permutation law. |
| π, `hπ`, `hMass` | A measurable finite random permutation with exactly all masses in `eq:luce-law`. `exponentialRace_order_probability` and `luce_map_eq_raceDraw` prove the representation. These do not assume a limiting law or any conditional-probability formula. |
| α, `hα` | Exactly α < 1. There is no added α > 0 or α ≥ 0 premise. The empty-cutoff convention is explicit below. |
| g, `Continuous g` | Every signed real continuous function on the literal subtype [0,α]. The extension is defined and proved to agree there; boundedness is derived from compactness. |
| `predictableChance` | θ[n,k] times the remaining-label indicator divided by the actual total remaining weight. Positivity of that denominator follows from remaining-set nonemptiness and positive weights. |
| `profileQuantile`, `profileDiagonal` | The inverse of F on nonnegative times, and f(x)exp(−t_x f(x))/D(t_x). Inverse identities and all nonzero denominators used on the interior are proved. No desired limit appears in the definitions. |
| `interiorFixedPoints` | The finite sum of unit Dirac masses for the fixed labels, with inverse rank convention, correct one-based locations and deterministic cutoff. Multiplicities are retained. |
| `FinitePointMeasure` and test F | Actual finite counting measures, as a subtype of mathlib `FiniteMeasure` with its induced weak topology. Quantifying over **all** bounded continuous functions of this state is the full convergence-in-law conclusion, not just a Laplace or moment statement. |
| `interiorIntensity` | Projection of the literal restricted Lebesgue density to [0,1]. Finiteness is derived, and mapping back to ℝ recovers that density measure exactly. Proof arguments hf/hα certify finiteness only. |
| `finitePoissonLaw` | Actual Poisson-count/iid-location mixture, with separate zero-intensity case. Its PRM property is proved through the joint count law; it is not made true by a definition. |

The final theorems have no endpoint lower-bound assumption, uniform rate
bound, symmetry, nonnegative-test restriction, continuity of f, auxiliary
concentration assumption, or assumed compensator convergence.

Nonvacuity is proved by `section3UnitWeights_normalized` and
`section3UnitWeights_profileLimit`: weights identically one with profile
identically one satisfy the assumptions. Their canonical exponential product
spaces are probability spaces; the sorting law supplies the Luce-law model.

### Endpoint and representation checks

- The paper's index k is Lean value k−1; each location is (k.val+1)/n.
  Grid-cell enumeration and the remaining-set rank bijection are proved.
- τ and the draw permutation have total extensions on tied clocks. The
  tie event has probability zero, and all uses of the sorting identities
  either assume distinctness in auxiliary lemmas or discharge it a.e.
- The arriving clock is included in W: survival is **≥**, not >. The proof
  does not take an uncountable intersection of fixed-time probability-one
  events; the weak-survival uniform limit has its own monotone-grid proof.
- `Ioc 0 α` and `Icc 0 α` have the same Lebesgue restriction, formally
  recorded by `interior_integral_eq_closed` and
  `interiorDensityMeasure_eq_closed`. Endpoint values of f and g do not
  affect the intensity/integral. The real-line fixed-point Dirac sum is
  recovered by `interiorFixedPoints_realMeasure`.
- α = 0 selects no labels and has zero intensity. If α < 0, the manuscript's
  [0,α] is interpreted as the empty set, so the sum/measure/integral vanish.
  The source writes “every α < 1” while its tα notation is meaningful in the
  nonnegative interior; this is an explicit interpretation of the empty case,
  not an assertion about an oriented integral of an undefined negative-domain
  profile. T < 0 likewise has an empty time index set. No substantive theorem
  is asserted at α = 1, which the source excludes.
- n = 0 is a harmless initial empty row. General statements restore all n
  using a proved filter-shift equivalence, so no positive-row premise is hidden.
- All manipulated integrals and expectations have integrability proofs;
  infinite L1 errors use eLpNorm and cannot be mistaken for zero by totalization.
  Positive-time band bounds and denominator inversions discharge their sign
  conditions before division. Poisson mixtures establish summability before
  interchanging sums and integrals.

## Proof-strategy deviations and interpretation issues

No mathematical gap requiring a stronger hypothesis was found. The substantive
race → quantile → denominator → survival replacement → independent variance
→ expectation → predictable Poisson mechanism is preserved.

1. Arrival concentration uses the proved variance/Chebyshev bound instead of
   invoking Hoeffding. The finite-grid/monotonicity upgrade is unchanged.
2. For deterministic expectation convergence, an L1 comparison is followed by
   dominated convergence for the fixed limiting profile. This is equivalent
   to the source's η-cutoff estimate and includes the fractional final cell.
   The stochastic survival/variance steps still explicitly remove the initial
   block, where the hard positive-time bounds are unavailable.
3. `Section3PoissonCriterion` feeds each continuous compensator test directly
   into the checked Section 2 likelihood and tightness proof. This avoids an
   unnecessary intermediate reformulation of weak-measure convergence in
   probability; it gives the same full bounded-continuous-law conclusion.
4. The reused Section 2 stopped likelihood proof derives a deterministic
   L∞ bound exp(K/(1−δ)) instead of the manuscript's L² bound. Its positive
   denominators and integrability are proved before cancellation. This is a
   proof-level strengthening under the same caps, not a new final assumption.
5. The canonical Poisson construction is identified with PRM by an explicit
   disjoint-count theorem. The required discrete Laplace uniqueness is proved
   by finite compact boxes and Stone–Weierstrass rather than cited informally.

These are the corrections/refinements of the initial Lean signature templates:
the placeholder names have been replaced by the exact declarations above;
actual W is exposed in a dedicated general theorem; arbitrary Luce-law
permutations are recovered without clock premises in Proposition/Corollary;
and full law convergence is expressed by all bounded continuous state tests.
The target mathematics, constants, quantifier order and hypotheses were not
weakened to make implementation easier.

## Separate proof audit and verification record

`audit/Section3.lean` imports the checked entry point and runs **32**
`#print axioms` commands on every main theorem and substantive bridges. All inspected transitive
dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.
There are no additional mathematical axioms. The actual output is retained
in `audit/section3-audit.log`.

This was not merely a text scan. The local import closure and substantive
proof bodies were inspected separately, including:

- exact finite-cell integrals, normalization, finite-grid event containments,
  arbitrary-space outer-measure transfer, and signed denominator estimates;
- shrinking-band expectation and independent-variance estimates, and removal
  of all positive-cutoff hypotheses using the initial mass bound;
- full race permutation masses, the finite-history conditional expectation,
  actual observations and their adaptedness;
- likelihood integrability and stopping removal, count tightness using the
  stopped row (without assuming bounded original expectations), and compact
  approximation with clipping to control tails;
- actual finite counting measures, the Poisson mixture's zero case,
  count/mass correspondence, and disjoint-count uniqueness.

The supplemental source scan found no `sorry`, `admit`, `sorryAx`, new `axiom`,
`unsafe`, `native_decide`, `implemented_by`, or `extern` in `Luce/*.lean`.
`audit/section3-source-scan.txt` records the no-match result. The import closure
is listed in `audit/section3-local-dependencies.txt`; build coverage is recorded
in `audit/section3-build-coverage.txt`.

Executed verification commands (from the project root, with pinned versions):

```powershell
lake env lean --version
git -C .lake/packages/mathlib rev-parse HEAD
lake build Luce.Section3CompensatorLimit
lake build Luce.Section3PoissonLaw
lake build Luce.Section3LuceCompensator
lake build Luce.Section3Poisson
lake build
lake env lean audit/Section3.lean
```

The individual proof modules and the full default build succeeded. The final
`lake build`, including the literal representation identities, reported
**3736 jobs** and exited with status **0**. It built `Luce.Section3Representations`,
`Luce.Section3`, and `Luce`. The final `lake env lean audit/Section3.lean` also
exited with status **0**, printing the full explicit types, expanded definitions,
and the 32 foundation-only axiom reports. The complete outputs are
`audit/section3-full-build.log` and `audit/section3-audit.log`.
Harmless existing/style/deprecation linter warnings remain; there are no
proof errors. Incremental failed attempts were fixed using compiler feedback;
only successful checked declarations are included in the entry point.

The mathematical TeX sources were not modified. Both recorded SHA256 hashes
were rechecked against the original values. The Lean toolchain, mathlib pin,
manifest, and pre-existing work were retained.
The exact version and hash output is saved in `audit/section3-environment.txt`.

## Section 5 deliverable appendix (separate from the Section 3 status above)

The Section 5 request named both `SECTION5_FORMALIZATION.md` (specification)
and `SECTION3_FORMALIZATION.md` (delivery). The complete Section 5 source
contract, notation dictionary, dependency map, exact theorem types, separate
proof/statement audits, build records, and unresolved issues are preserved in
[SECTION5_FORMALIZATION.md](SECTION5_FORMALIZATION.md). This appendix records
the Section 5 result without overwriting the independent Section 3 work.

**Section 5 remains incomplete.** Target: `fixed_points.tex:963–1320`,
“Short cycles,” proving Theorem 1.4 (`thm:short-cycles`, lines 288–299): under
positive normalized weights, Assumption 1.1 (positive measurable L1 profile,
223–229) and Assumption 1.2 (uniform endpoint lower bound, 255–260), the cycle
count vector converges to independent Poisson variables with the cyclic
integral means, both weakly and in total variation. No weakened final theorem
or assumed proof interface has been supplied.

Checked source correspondence:

- Lemma 5.1 (977–994): `Luce.ProfileLimit.moderate_reservoir` and
  `moderate_reservoir_with_remaining_rate`, in `Luce/Section5Reservoir.lean`.
  Inputs are only `w`, `f`, `ProfileLimit w f`, `α`, `α<1`; the proof derives
  uniform constants and the arbitrary fixed-deletion consequence.
- Lemma 5.3 (1106–1137): `Luce.finite_insertion_path`, in
  `Luce/Section5FiniteInsertion.lean`, with only positive `w : Weights n`,
  `ell,m : ℕ`, and `v : Fin n`. It bounds the actual expectation of the sum
  over distinct ordered sources of window-probability products by
  `(2*(ell+m+2)+1)^m`. The endpoint may repeat a source. Integrability and
  correspondence to the original real density integral are separate proved
  theorems, not assumptions.
- Cycle formula/root factors (164–172, 303–304, 1281–1284):
  `Luce.Section5.cycleCount_eq_tuple_sum` and `rootedCycleCollection_card`,
  in `Luce/Section5Cycles.lean`, with finite label type, decidable equality,
  actual permutation, length/multiplicity parameters only. Fixed points,
  inverse invariance, disjointness and empty collections are covered.

Dependency map: positive superlevel sets + actual L1 cell comparison imply
the reservoir. `Section5Insertion` proves exact window indices, finite rank
perturbation and path counts. `Section5Resampling` proves independent-copy
swap invariance. `Section5WindowProbability` proves conditional products,
Tonelli conversion and expected insertion counts. `Section5FiniteInsertion`
transfers these to the paper's open windows and real expectation, including
the row-probability bound. `Section5Cycles` independently proves the exact
root-count and falling-factorial factors. Every new module is imported by
`Luce/Section5.lean`, itself imported by the default `Luce.lean` build.

Further checked progress in the resumed Section 5 work:

- `ProfileLimit.weighted_bulk_cylinder` proves the actual weighted bulk bound
  with uniform constants and unrestricted positive marked rates.
- `ghost_cylinder_bound` and `added_predecessor` prove the exact window
  probability comparison and collision-counting expectation estimate.
- `section5_deleted_order_statistics` and `section5_deleted_gap_rate` prove
  the uniform finite-deletion time/rate controls, including strict survival.
- `ProfileLimit.high_rate_cycles_vanish` proves the high-rate half of
  Proposition 5.4, the literal `M→∞` limit of `limsup_n E V_(n,L)(H_n(M))`.
  Its only hypotheses are the normalized positive weight array and its
  actual L1 positive profile limit. Half-mass, integrability and limsup
  boundedness are proved. `lowRateDensity_small` proves low-label scarcity.
- `bulk_cycle_factorial_eq_assignment_sum` proves the full finite factorial
  expansion for cycles entirely within the actual bulk set. Its explicit
  global label bijection and positive rotational divisor preserve every
  multiplicity; no invariant-cutoff assumption is introduced.
- `ProfileLimit.interior_ghostWindowLength_uniform` derives the actual
  interior expected-window bound from the reservoir, with one constant and
  eventual threshold for every `ell≤L`. Integrability and finite upper
  window endpoints are proved, as is the occupation identity it uses.

Remaining: Lemma 5.2's microscopic gap factorization, marked insertion/Taylor
calculation, mixed moments and cyclic local law; the low-rate cycle half of
Proposition 5.4; Lemma 5.5 and its beta moment; joint factorial-moment
convergence; endpoint removal and finite intensities; and the final Poisson
and total-variation limits. The latest finite cutoff correspondence and
window-occupation status is recorded in `SECTION5_FORMALIZATION.md`.
No placeholder proofs are supplied for any remaining obligation. The detailed
record distinguishes missing formal dependencies from mathematical gaps;
no definite contradiction was found. It retains the ε₀≥1 and order-index
boundary cases rather than adding assumptions to exclude them.

Reproduce with `lake build` and `lake env lean audit/Section5.lean`. The
environment remains Lean 4.33.1 and mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. Actual build/type/axiom output is
saved under `audit/section5-*.log`; final verification status is in the full
Section 5 record. Main proved results have only `propext`, `Classical.choice`,
and `Quot.sound` as transitive axioms. The proof audit also inspected the
local import closure recorded under `audit/`; the separate statement audit expanded custom
definitions and checked every binder, source/rank orientation, root factor,
null-set convention and denominator/integrability requirement. An explicit
constant-one array satisfies all standing assumptions. Mathematical source
files and dependency pins remain unchanged.

Final Section 5 verification for this run: `lake build` exited 0 with 3768
jobs, and `lake env lean audit/Section5.lean` exited 0 with all 65 actual
axiom queries and full-type/definition queries completed. All 21 Section 5
files are included in the default build; the transitive local closure has
51 files. The main results use only the permitted foundational axioms listed
above. The final full logs and independent statement-audit conclusions are
recorded in `SECTION5_FORMALIZATION.md`. Theorem 1.4 remains unproved; this
appendix reports compiling partial progress, not completion of Section 5.

### Focused continuation: Lemma 5.2

The later request to formalize Lemma 5.2 is implemented in
`Luce/Section5Lemma52.lean`. Its main declarations are
`Luce.section5_bounded_marked_asymptotic`, `Luce.section5_cyclic_local`, and
`Luce.section5_lemma52`. The whole lemma includes the signed cyclic limit
on the literal closed cube and a weighted cylinder bound for every row.
The proof derives the exact joint gap law, insertion identity, mixed moments,
uniform Taylor/expectation error and cyclic grid/profile passage from the
paper's hypotheses. No missing microscopic estimate is assumed.

The initial eventual-row translation of the weighted bound was corrected
against source lines 1010–1013: finitely many early rows are absorbed into
one positive constant, with zero-row cases proved separately. The only
proof reorganizations are the bounded-rate dominated-convergence treatment
of null diagonals and the equivalent integrable product-envelope organization
of the `L¹` passage. No stronger final assumptions were introduced.

The complete source correspondence, actual theorem statement with every
assumption, dependency map, endpoint checks, independent audits and final
verification commands are recorded in `SECTION5_FORMALIZATION.md` under
“Focused continuation: Lemma 5.2”. This appendix remains a Section 3 record;
the Section 5 account is linked here to satisfy the requested filename.
Theorem 1.4 and the remaining Section 5 results listed there are still
outside this completed lemma.

Final verification of this focused continuation (2026-09-10): `lake build`
exited 0 with **3790 jobs**, including all **43** Section 5 modules.
`lake env lean audit/Lemma52.lean` and
`lake env lean audit/Section5.lean` exited 0 with **16** and **69** axiom
queries, respectively. The separate proof and statement audit commands
`lake env lean audit/Lemma52Proof.lean` and
`lake env lean audit/Lemma52StatementCheck.lean` also exited 0. The proof
audit checked **47,107** transitive declarations and found only `propext`,
`Classical.choice`, and `Quot.sound`, with no unsafe/partial dependency.
The independent statement audit confirmed the actual final all-row bound
and found no remaining mismatch. Logs and reports are under
`audit/lemma52-*`; exact commands and source hashes are recorded in the
Section 5 document. Lean remains **4.33.1**, and mathlib remains
`0df444a360eaa60ab8c11dca51a86af692955474`. No mathematical source or pin was
changed. Lemma 5.2 has no remaining proof obligations.

### Further Section 5 continuation: Proposition 5.4 (2026-09-11)

Both exceptional-rate limits are now proved in
`Luce/Section5ExceptionalLow.lean`, main theorem
`Luce.section5_proposition54`. Its assumptions are exactly the positive
weight array, mean-one normalization, profile limit, endpoint assumption,
and arbitrary `L : ℕ`. The low-rate proof includes the actual restricted
ghost-cycle comparison, finite-window density bound, nonnegative path
row sum, orbit charging inequality and successive cutoff limits. No new
mathematical assumption or unproved intermediate estimate was introduced.

The full build exited 0 with **3794 jobs**, including all **47** Section 5
modules. The focused statement audit, checked-body proof audit, and
aggregate Section 5 audit also exited 0. The proof audit traversed
**46,029** declarations and found only `propext`, `Classical.choice`, and
`Quot.sound`, with no unsafe/partial dependency. The separate statement
audit checked the actual expanded assumptions, counts, strict cutoffs,
endpoints and limit order. Full correspondence, the exact Lean statement,
commands, logs and remaining obligations are in `SECTION5_FORMALIZATION.md`
under “Completed Proposition 5.4”. The manuscript and version pins are
unchanged. Lemma 5.5 and Theorem 1.4 remain unfinished.
