import Luce.FiniteAdaptedBernoulli
import Luce.ConvergenceInProbability
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Independent closed target for Proposition 6.11, `prop:sp-fixed-martingale`.
The row spaces and row lengths may vary. Conditional probabilities are derived
from adapted zero-one observations; no independence or integrability assumptions
are added. Positivity of the normalization is required only eventually by its limit. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace Luce.Section6.Proposition611Contract

def proposition611 : Prop :=
  ∀ (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (N : ℕ → ℕ) (B : ∀ n, FiniteAdaptedBernoulli (P n) (N n)) (v : ℕ → ℝ),
    Tendsto v atTop atTop →
    ConvergesInProbability P (fun n ω =>
      ((∑ k, (B n).probability k ω) - v n) / Real.sqrt (v n)) 0 →
    ConvergesInProbability P (fun n ω =>
      (∑ k, ((B n).probability k ω)^2) / v n) 0 →
    (∀ F : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ ω,
      F (((∑ k, (B n).observationReal k ω) - v n) / Real.sqrt (v n)) ∂P n)
      atTop (𝓝 (∫ x, F x ∂ProbabilityTheory.gaussianReal 0 1))) ∧
    (Tendsto (fun n => (∫ ω, ∑ k, (B n).probability k ω ∂P n) / v n)
      atTop (𝓝 1) →
      Tendsto (fun n => (∫ ω, ∑ k, (B n).observationReal k ω ∂P n) / v n)
        atTop (𝓝 1))

end Luce.Section6.Proposition611Contract
