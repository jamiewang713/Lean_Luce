# Proposed Section 2 compensator statement

This is a statement proposal for approval. The substantive proposition has
not been proved or asserted. The proposal lives outside production imports
in `proposals/Section2Compensator.lean`.

## Exact source

`fixed_points.tex:581-584`, label `eq:compensator-measure`, defines

\[
A_n=\sum_{k=1}^n p_{n,k}\delta_{k/n}
\]

The exact source passage is:

```latex
The random measure
\begin{equation}\label{eq:compensator-measure}
 A_n:=\sum_{k=1}^n p_{n,k}\delta_{k/n}
\end{equation}
is the predictable compensator of $\Xi_n$ in draw order.
```

The fixed-point measure is defined at line 150,
`eq:fixed-process`; the defining full Luce permutation law is at line 142,
`eq:luce-law`. The explicit conditional probability is at line 575,
`eq:predictable-p`, now proved as
`Luce.predictable_fixed_point_probability` in `Luce/PredictableProbability.lean`.

## Proposed definitions

Fix a row size `n : ℕ`, deterministic positive weights `w : Weights n`, and
a random draw-order permutation `π : Ω → Equiv.Perm (Fin n)`. For
`k : Fin n`, use

\[
x_k=\frac{k.\mathrm{val}+1}{n},\qquad
I_k(\omega)=\mathbf1_{\{(\pi(\omega))^{-1}(k)=k\}},\qquad
p_k(\omega)=\operatorname{predictableChance}(w,\pi(\omega),k).
\]

The approved existing formula for the last expression is

\[
p_k(\omega)=
\frac{w_k\mathbf1_{\{k\le(\pi(\omega))^{-1}(k)\}}}
{w.\operatorname{total}(\operatorname{remaining}(\pi(\omega),k))}.
\]

For every `m : ℕ`, define cumulative measures

\[
\Xi_m(\omega)=\sum_{k.\mathrm{val}<m}I_k(\omega)\delta_{x_k},
\qquad
A_m(\omega)=\sum_{k.\mathrm{val}<m}p_k(\omega)\delta_{x_k}.
\]

These denote partial sums within the fixed row of size `n`; the manuscript's
terminal objects are `fixedPointMeasure π = fixedPointMeasurePrefix π n`
and `compensatorMeasure w π = compensatorMeasurePrefix w π n`. At time zero
the sums are empty, and after time `n` they remain constant.

Each outcome produces a `Measure ℝ`. Coefficients are converted by
`ENNReal.ofReal`, as Lean measures take nonnegative extended-real scalars.
The indicator is zero or one and the existing choice bounds give
`0 ≤ p_k ≤ 1`, so this conversion does not change the intended coefficients.
Finiteness and measurability as measure-valued maps are explicit conclusions
below; they are not additional assumptions or an informal interpretation
of the word "random". Packaging into `FiniteMeasure ℝ` is not part of this
proposal. The target measurable structure on `Measure ℝ` is mathlib's
evaluation sigma algebra. No weak-topology convergence claim is included.

The manuscript explicitly treats the point measure as a measure on `[0,1]`
at `fixed_points.tex:269`. This proposal instead uses the usual Borel real
line and explicitly concludes that both measures give zero mass outside
`[0,1]`. This is a representation choice requiring approval. It corresponds
mathematically to extension by zero along the inclusion `[0,1] → ℝ`;
no formal equivalence theorem with subtype measures is asserted here.
The atom locations actually lie in `(0,1]`. No assumption `0 < n` is
needed: when `n = 0`, there are no `Fin n` indices and the measure sums
vanish; no atom at a divided-by-zero location is produced.

`drawFiltration π hπ` is a structure wrapper with value definitionally equal
to the approved `drawHistory π m` at every `m`. Its only proof is the
routine implication `j.val < a ≤ b → j.val < b`, establishing monotonicity,
together with the existing `drawHistory_le π hπ` for ambient inclusion.
Thus an arbitrary filtration or its existence is not assumed. There is
no completion, enlargement, or index shift of the approved history.

For each deterministic spatial test `g : ℝ → ℝ`, define

\[
C_g(m,\omega)=\int g\,dA_m(\omega),\qquad
M_g(m,\omega)=\int g\,d\Xi_m(\omega)-C_g(m,\omega).
\]

The proposal requires `g` to be Borel measurable, with no global bound.
Only the finitely many finite real values `g(x_k)` occur. Spatial
integrability is included as a conclusion, so the intended integrals
are not left subject to Lean's default value for nonintegrable functions.
The two tested processes are also explicitly required to be integrable
over the sample space with respect to `P` at every time. These are derived
conclusions, without an additional boundedness or integrability hypothesis
on `g`. `testedFixedPoint π g m` denotes the first tested process.

## Complete proposed statement

The declaration `CompensatorStatement : Prop` contains the following
unasserted proposition. All definitions in this display are in namespace
`Luce.Section2CompensatorProposal`.

```lean
∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}
  (P : Measure Ω) [_hP : IsProbabilityMeasure P] (w : Weights n)
  (π : Ω → Equiv.Perm (Fin n))
  (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π),
  (∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ) →
  (∀ (m : ℕ) (ω : Ω),
    IsFiniteMeasure (fixedPointMeasurePrefix π m ω) ∧
    IsFiniteMeasure (compensatorMeasurePrefix w π m ω)) ∧
  (∀ m : ℕ, Measurable (fixedPointMeasurePrefix π m) ∧
    Measurable (compensatorMeasurePrefix w π m)) ∧
  (∀ (m : ℕ) (ω : Ω),
    fixedPointMeasurePrefix π m ω (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
    compensatorMeasurePrefix w π m ω (Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧
  ∀ g : ℝ → ℝ, Measurable g →
    (∀ (m : ℕ) (ω : Ω), Integrable g (fixedPointMeasurePrefix π m ω) ∧
      Integrable g (compensatorMeasurePrefix w π m ω)) ∧
    (∀ m : ℕ, Integrable (testedFixedPoint π g m) P ∧
      Integrable (testedCompensator w π g m) P) ∧
    IsStronglyPredictable (drawFiltration π hπ) (testedCompensator w π g) ∧
    Martingale (centeredTestedProcess w π g) (drawFiltration π hπ) P
```

Here `Ω`, `mΩ`, `P`, and `IsProbabilityMeasure P` give an arbitrary
probability space. `u` is only a Lean universe parameter. Positivity of
all deterministic weights is part of `Weights n`. The explicit target
sigma algebra `⊤` gives the finite permutation space its discrete
measurability. The singleton probability equalities specify exactly the
full Luce product law for every deterministic permutation `σ`.

There is no clock model, independence assumption, rate normalization,
canonical sample space, positive-probability-history assumption, or
assumed conditional-choice identity. Integrability and measurability
obligations are conclusions or must be derived from the stated data.

There are no new uniform or asymptotic constants. The deterministic location
`x_k` depends only on `n` and `k`; the rates depend only on the given weight
vector and label. The remaining bound variables are the outcome `ω`, prefix
time `m`, spatial point of integration, test function `g`, and martingale
times `a ≤ b`. The only sample-space typeclass assumptions are exactly
`MeasurableSpace Ω` and `IsProbabilityMeasure P`. All real-space, finite-index,
and classical decidability instances are fixed implementation instances;
none is an additional assumption on the probability model.

The conclusion is inventoried in the order of the Lean proposition:

| Exact quantified component | Mathematical role and correspondence |
| --- | --- |
| `∀ (m : ℕ) (ω : Ω), IsFiniteMeasure XiPrefix ∧ IsFiniteMeasure APrefix` | Both finite atomic sums are finite measures for every outcome and every prefix. This makes the finite-measure interpretation explicit. |
| `∀ m, Measurable (fixedPointMeasurePrefix π m) ∧ Measurable (compensatorMeasurePrefix w π m)` | Both maps from outcomes to measures are random measures in the evaluation-sigma-algebra sense, rather than merely collections of outcome-dependent measures. |
| `∀ m ω, XiPrefix ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧ APrefix ((Set.Icc (0 : ℝ) 1)ᶜ) = 0` | The explicit real-line representation has zero mass outside the manuscript's state space `[0,1]`. This is a conclusion derived from the deterministic locations, not a support hypothesis. No subtype-measure equivalence theorem is claimed. |
| `∀ g : ℝ → ℝ, Measurable g → ...` | Every deterministic real-valued Borel spatial test is covered. There is no global boundedness or integrability assumption on the test. |
| `∀ m ω, Integrable g XiPrefix ∧ Integrable g APrefix` | The spatial integrals against both atomic measures exist in the usual finite-valued sense for every outcome. This follows from finite support and is a conclusion, not an extra test restriction. |
| `∀ m, Integrable (testedFixedPoint π g m) P ∧ Integrable (testedCompensator w π g m) P` | Each uncentered tested process is integrable over the original probability space. This is distinct from the preceding spatial integrability and explicitly supplies ordinary martingale integrability after subtraction. It must be derived from the probability model and bounded finite sums. |
| `IsStronglyPredictable (drawFiltration π hπ) (testedCompensator w π g)` | The cumulative compensator tested against `g` is known from the appropriate preceding draw history. The history is exactly the existing `drawHistory`. |
| `Martingale (centeredTestedProcess w π g) (drawFiltration π hπ) P` | All conditional-expectation identities for the centered cumulative tested process hold with respect to the exact draw filtration and original probability law. This is the substantive compensator assertion. |

In the table, `XiPrefix` and `APrefix` abbreviate only the displayed full
applications of `fixedPointMeasurePrefix` and `compensatorMeasurePrefix`;
they are not additional definitions or variables of the proposition.

## Meaning of the compensator conclusion

`IsStronglyPredictable` means that `C_g(0)` is measurable at history zero
and `C_g(m+1)` is measurable with respect to `drawHistory π m`.
The pinned `Martingale` definition contains strong adaptedness and the
conditional-expectation identities, for every `a ≤ b`,

\[
E_P[M_g(b)\mid\mathcal H_a]=M_g(a)\quad P\text{-almost surely}.
\]

Integrability is not a field of that definition. For the complete real
target it follows from `Martingale.integrable`; in addition, this proposal
explicitly includes sample integrability of each uncentered tested process
as a conclusion. Their difference is consequently integrable as well.

Taking `g` to be the indicator of any Borel spatial set gives the
cumulative count in that set minus its cumulative compensator as a
martingale. The assertion therefore retains conditional information at
every draw; equality of expected terminal totals is not substituted.

In this finite deterministic-support setting, the proposed martingale
characterization is mathematically equivalent to the predictable-testing
identity

\[
E\sum_k H_k I_k=E\sum_k H_kp_k
\]

for every nonnegative, possibly extended-valued family `H_k` measurable
with respect to the history before draw `k`. Successive martingale
increments recover the one-step conditional mean. Multiplication by
bounded history-measurable tests and then monotone approximation recover
all nonnegative tests. Conversely, tests supported at one draw and one
history-measurable event recover the conditional mean and hence the
tested martingales. Deterministic spatial tests are evaluated at `x_k`.

This equivalence is explained to make the mathematical choice reviewable;
it is not a separate Lean theorem asserted or proved by this proposal.
The proposition to approve is exactly the displayed tested martingale
and predictability statement, with its finiteness, measurability, support,
spatial integrability, and sample integrability conclusions.

## Existing declarations and remaining proof obligations

Production inputs already available:

- `Luce.predictable_fixed_point_probability`,
  `Luce/PredictableProbability.lean`: the approved conditional expectation
  identity under precisely the model assumptions above.
- `Luce.measurable_predictableChance_history`,
  `Luce.integrable_predictableChance`, and
  `Luce.integrable_fixed_point_indicator`,
  `Luce/ConditionalProbabilityBasics.lean`.
- `Luce.drawHistory_le` in the same module and the exact definition
  `Luce.drawHistory` in `Luce/DrawHistory.lean`.
- The positivity, upper bounds, and algebraic formula for the explicit
  probabilities in `Luce/Model.lean`.

Pinned mathlib declarations inspected in source:

- `MeasureTheory.IsStronglyPredictable.iff_measurable_add_one`,
  `Mathlib/Probability/Process/Predictable.lean:252`: exactly
  `IsStronglyPredictable F u ↔ StronglyMeasurable[F 0] (u 0) ∧
  ∀ m, StronglyMeasurable[F m] (u (m+1))`.
- `MeasureTheory.martingale_nat`,
  `Mathlib/Probability/Martingale/Basic.lean:479`: for a complete target
  normed space and finite measure, strong adaptedness, integrability at
  every time, and `f m =ᵐ[P] P[f (m+1) | F m]` imply `Martingale f F P`.
- `MeasureTheory.Martingale.integrable`, same module, at line 98:
  a real-valued martingale is integrable at each time; the complete-space
  assumption is satisfied by the real target.
- `MeasureTheory.martingale_martingalePart`,
  `Mathlib/Probability/Martingale/Centering.lean:176`: under strong
  adaptedness, integrability, completeness, and a sigma-finite filtration,
  the process minus its sum of conditional expected increments is a
  martingale. This is an alternative route, not a new model assumption.
- `MeasureTheory.Measure.measurable_measure` and
  `MeasureTheory.Measure.measurable_of_measurable_coe`,
  `Mathlib/MeasureTheory/Measure/GiryMonad.lean:77` and `:55`: a map into
  measures is measurable exactly when evaluation at every measurable
  set is measurable.
- `MeasureTheory.Measure.measurable_dirac` and
  `Measurable.smul_measure`, same module, at lines 110 and 71.
- `MeasureTheory.lintegral_dirac`,
  `Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean:67`, evaluates
  an arbitrary nonnegative test against a Dirac measure when singletons
  are measurable; the real line satisfies this condition.
- `MeasureTheory.lintegral_smul_measure` and
  `MeasureTheory.lintegral_finsetSum_measure`,
  `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`: scalar and finite
  measure sums distribute over the nonnegative integral.

Remaining work, after approval: verify the atomic-measure conclusions
including support, identify tested integrals with their finite sums,
establish spatial and sample integrability and tested predictability,
and derive the martingale one-step identity from the
already proved conditional fixed-point probability. No such substantive
proof is included in this proposal.

## Verification

Typecheck command: `lake env lean proposals/Section2Compensator.lean`.
Result: PASS, exit 0, with no warnings. The printed dependency audit for
`CompensatorStatement` and the structural `drawFiltration` definition is
`[propext, Classical.choice, Quot.sound]`. The full printed statement and
dependency audit are recorded in `audit/section2-compensator-statement.txt`.

Typechecking establishes only that the definitions and proposed proposition
are well-formed. It does not prove `CompensatorStatement`. The only proof
body introduced here is the elementary structural filtration wrapper.
No axiom, admitted claim, or substantive theorem proof is introduced.
