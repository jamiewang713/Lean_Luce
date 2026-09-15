import Luce.Section2ConvergenceInProbability
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-! # Weak convergence in probability of random finite measures

For `fixed_points.tex`, `eq:poisson-criterion`, this definition uses open
neighborhoods in the actual weak topology on finite measures. Convergence
of integral coordinates is a consequence of continuity, not a substituted
definition. Row probability spaces may vary. Measure values on arbitrary
events are outer probabilities; no measurability of all weak-open inverse
images is presumed.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace Luce

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Convergence to a deterministic finite measure in probability, tested
against every open neighborhood for the weak topology. -/
def WeakMeasureConvergesInProbability (P : ∀ n, Measure (Ω n))
    (A : ∀ n, Ω n → FiniteMeasure X) (ν : FiniteMeasure X) : Prop :=
  ∀ U : Set (FiniteMeasure X), IsOpen U → ν ∈ U →
    Tendsto (fun n => (P n).real {ω | A n ω ∉ U}) atTop (𝓝 0)

namespace WeakMeasureConvergesInProbability

variable {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
  {A : ∀ n, Ω n → FiniteMeasure X} {ν : FiniteMeasure X}

/-- Every bounded continuous real integral coordinate inherits convergence
in probability from the actual weak-neighborhood criterion. -/
theorem integral (hA : WeakMeasureConvergesInProbability P A ν) (f : X →ᵇ ℝ) :
    ConvergesInProbability P (fun n ω => ∫ x, f x ∂(A n ω : Measure X))
      (∫ x, f x ∂(ν : Measure X)) := by
  intro ε hε
  let U : Set (FiniteMeasure X) :=
    {μ | |(∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂(ν : Measure X)| < ε}
  have hU : IsOpen U :=
    isOpen_lt ((FiniteMeasure.continuous_integral_boundedContinuousFunction f).sub
      continuous_const).abs continuous_const
  have hν : ν ∈ U := by simpa only [U, Set.mem_ofPred_eq, sub_self, abs_zero] using hε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (hA U hU hν)
  intro n
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  change ε < |(∫ x, f x ∂(A n ω : Measure X)) - ∫ x, f x ∂(ν : Measure X)| at hω
  change ¬ |(∫ x, f x ∂(A n ω : Measure X)) - ∫ x, f x ∂(ν : Measure X)| < ε
  exact not_lt.mpr hω.le

end WeakMeasureConvergesInProbability
end Luce
