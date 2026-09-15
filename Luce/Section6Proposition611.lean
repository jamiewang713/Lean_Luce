import Luce.BernoulliCLT
import Luce.Section6Proposition611Contract

/-! Proposition 6.11 (`prop:sp-fixed-martingale`) for actual finite adapted rows. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction

namespace Luce.FiniteAdaptedBernoulli

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {N : ℕ} (B : FiniteAdaptedBernoulli μ N)

theorem toProcess_cltCount (ω : Ω) :
    B.toProcess.cltCount N ω = ∑ k, B.observationReal k ω := by
  rw [BernoulliProcess.cltCount, ← Fin.sum_univ_eq_sum_range]
  simp only [B.toProcess_observation]

theorem toProcess_cltMass (ω : Ω) :
    B.toProcess.cltMass N ω = ∑ k, B.probability k ω := by
  rw [BernoulliProcess.cltMass, ← Fin.sum_univ_eq_sum_range]
  simp only [B.toProcess_probability]

theorem toProcess_cltSquares (ω : Ω) :
    B.toProcess.cltSquares N ω = ∑ k, (B.probability k ω)^2 := by
  rw [BernoulliProcess.cltSquares, ← Fin.sum_univ_eq_sum_range]
  simp only [B.toProcess_probability]

theorem integral_observation_sum_eq_probability_sum :
    (∫ ω, ∑ k, B.observationReal k ω ∂μ) = ∫ ω, ∑ k, B.probability k ω ∂μ := by
  have h := B.toProcess.integral_sum_observation N
  change (∫ ω, B.toProcess.cltCount N ω ∂μ) = ∫ ω, B.toProcess.cltMass N ω ∂μ at h
  simpa only [B.toProcess_cltCount, B.toProcess_cltMass] using h

end Luce.FiniteAdaptedBernoulli

namespace Luce.Section6

/-- The complete closed Proposition 6.11. The central limit proof is independent
of the expectation premise, which is used only for the expectation conclusion. -/
theorem proposition611 : Proposition611Contract.proposition611 := by
  intro Ω mΩ P hP N B v hv hA hB
  constructor
  · intro F
    have h := BernoulliCLT.boundedContinuous_tendsto P (fun n => (B n).toProcess) N hv
      (by simpa only [FiniteAdaptedBernoulli.toProcess_cltMass] using hA)
      (by simpa only [FiniteAdaptedBernoulli.toProcess_cltSquares] using hB) F
    simpa only [FiniteAdaptedBernoulli.toProcess_cltCount] using h
  · intro hmean
    simpa only [FiniteAdaptedBernoulli.integral_observation_sum_eq_probability_sum] using hmean

end Luce.Section6
