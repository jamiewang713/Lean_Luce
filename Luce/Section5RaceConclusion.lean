import Luce.Section5VectorTotalVariation
import Luce.Section4CountableLawConvergence

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace Luce

theorem EndpointShellAssumption.cycle_vector_weak
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (L : ℕ)
    (F : (Fin L → ℕ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ z, F (cycleCountVector L (raceRankPermutation z))
      ∂exponentialRace (w n)) atTop (𝓝 (∫ x, F x ∂cycleVectorPoissonLaw f L)) := by
  have ht := hend.cycle_vector_totalVariation hnorm hf L
  change Tendsto (fun n => cycleVectorTotalVariation
    (raceCycleVectorLaw (w n) L : Measure (Fin L → ℕ))
    (cycleVectorPoissonProbability f L : Measure (Fin L → ℕ))) atTop (𝓝 0) at ht
  simp_rw [cycleVectorTotalVariation_eq_countable] at ht
  have h := CountableLaw.tendsto_bounded_integrals_of_totalVariation ht F
  change Tendsto (fun n => ∫ x, F x ∂((exponentialRace (w n)).map
    (fun z => cycleCountVector L (raceRankPermutation z)))) atTop
    (𝓝 (∫ x, F x ∂cycleVectorPoissonLaw f L)) at h
  simpa only [integral_map (measurable_race_permutation_statistic (cycleCountVector L)).aemeasurable
    F.continuous.measurable.aestronglyMeasurable] using h

end Luce
