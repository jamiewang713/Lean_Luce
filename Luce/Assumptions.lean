import Luce.Model
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# The manuscript's finite-mean assumptions

Source: `fixed_points.tex`, Section 1, equations `eq:normalization` and
`eq:step-profile`, and Assumptions 1.1 (`ass:profile`) and 1.2 (`ass:endpoint`).

These are predicates on the weight array, not declarations that the predicates
hold. The existing `Weights` type supplies the model's strictly positive rates.
The paper's label `k` is represented by a `Fin n` element with value `k - 1`.
Row zero has no labels and contributes only an irrelevant initial sequence term.
The user approved Lebesgue measurability for Assumption 1.1 on 2026-09-10.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Luce

/-- A triangular array of the model's strictly positive weights. -/
abbrev WeightArray := (n : ℕ) → Weights n

/-- Mean-one normalization, `eq:normalization`. This is separate from both
numbered assumptions, just as in the manuscript. -/
def NormalizedWeights (w : WeightArray) : Prop :=
  ∀ n : ℕ, 0 < n → (1 / (n : ℝ)) * (∑ i : Fin n, (w n).rate i) = 1

/-- The exact step profile of `eq:step-profile`.
The `Fin n` index `i` represents paper label `i.val + 1`, whose cell is
`i.val / n < x ≤ (i.val + 1) / n`. The finite sum is zero outside `(0, 1]`
and on the empty row; neither extension affects the profile limit. -/
noncomputable def stepProfile (w : WeightArray) (n : ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ i : Fin n,
    if (i.val : ℝ) / (n : ℝ) < x ∧ x ≤ ((i.val : ℝ) + 1) / (n : ℝ)
    then (w n).rate i else 0

/-- Lebesgue measure restricted to the profile's domain `(0, 1)`. -/
noncomputable def profileMeasure : Measure ℝ :=
  volume.restrict (Set.Ioo (0 : ℝ) 1)

/-- The convergence in `eq:L1-profile`, expressed using the extended
nonnegative `L¹` seminorm. Infinite errors remain infinite, rather than taking
the default value of a nonintegrable real Bochner integral. Measurability and
pointwise positivity of the limiting profile belong to Assumption 1.1. -/
def ProfileL1Convergence (w : WeightArray) (f : ℝ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => eLpNorm (fun x => stepProfile w n x - f x) 1 profileMeasure)
    atTop (𝓝 0)

/-- The limiting profile in Assumption 1.1. `NullMeasurable` expresses the
approved Lebesgue measurability on `(0, 1)`, and positivity is pointwise there.
Values outside the interval are unconstrained. Integrability and unit mass
are not inserted as additional hypotheses. -/
def ProfileLimit (w : WeightArray) (f : ℝ → ℝ) : Prop :=
  NullMeasurable f profileMeasure ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x) ∧
    ProfileL1Convergence w f

/-- Assumption 1.1, `ass:profile`, equation `eq:L1-profile`.
There exists a Lebesgue-measurable, pointwise positive limiting profile to
which the step profiles converge in `L¹(0, 1)`. -/
def ProfileAssumption (w : WeightArray) : Prop :=
  ∃ f : ℝ → ℝ, ProfileLimit w f

/-- Assumption 1.2, `ass:endpoint`, equation `eq:endpoint-lower`.
One pair of strictly positive constants and one threshold work for all
subsequent rows and every label in the specified closed terminal neighborhood.
No upper bound on `ε₀` is imposed. -/
def EndpointAssumption (w : WeightArray) : Prop :=
  ∃ γ ε₀ : ℝ, ∃ n₀ : ℕ,
    0 < γ ∧ 0 < ε₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ k : Fin n,
        (1 - ε₀) * (n : ℝ) ≤ (k.val : ℝ) + 1 →
          γ ≤ (w n).rate k

end Luce
