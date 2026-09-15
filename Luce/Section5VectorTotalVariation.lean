import Luce.Section5FullPointProbability
import Luce.Section4CountableTotalVariation

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Luce

def raceCycleVectorLaw {n : ℕ} (w : Weights n) (L : ℕ) : ProbabilityMeasure (Fin L → ℕ) :=
  ⟨(exponentialRace w).map (fun z => cycleCountVector L (raceRankPermutation z)),
    (exponentialRace w).isProbabilityMeasure_map
      (measurable_race_permutation_statistic (cycleCountVector L)).aemeasurable⟩

def cycleVectorPoissonProbability (f : ℝ → ℝ) (L : ℕ) : ProbabilityMeasure (Fin L → ℕ) :=
  ⟨cycleVectorPoissonLaw f L, inferInstance⟩

/-- The generic countable-space TV is exactly the frozen contract's
supremum over event differences, with no change of convention. -/
theorem cycleVectorTotalVariation_eq_countable {L : ℕ}
    (μ ν : ProbabilityMeasure (Fin L → ℕ)) :
    cycleVectorTotalVariation (μ : Measure (Fin L → ℕ)) (ν : Measure (Fin L → ℕ)) =
      CountableLaw.probabilityTotalVariation μ ν := by
  unfold cycleVectorTotalVariation CountableLaw.probabilityTotalVariation
  congr 1
  ext r
  constructor
  · rintro ⟨A,hA⟩
    exact ⟨A,hA.symm⟩
  · rintro ⟨A,hA⟩
    exact ⟨A,hA.symm⟩

theorem raceCycleVectorLaw_real_singleton {n : ℕ} (w : Weights n) (L : ℕ)
    (q : Fin L → ℕ) :
    (raceCycleVectorLaw w L : Measure (Fin L → ℕ)).real {q} =
      (exponentialRace w).real {z | cycleCountVector L (raceRankPermutation z) = q} := by
  change ((exponentialRace w).map (fun z => cycleCountVector L (raceRankPermutation z))).real {q} = _
  rw [measureReal_def, Measure.map_apply_of_aemeasurable
    (measurable_race_permutation_statistic (cycleCountVector L)).aemeasurable
    (measurableSet_singleton q)]
  rfl

/-- Full cycle-count vector convergence in the exact total-variation
convention of the frozen contract. -/
theorem EndpointShellAssumption.cycle_vector_totalVariation
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (L : ℕ) :
    Tendsto (fun n => cycleVectorTotalVariation
      ((exponentialRace (w n)).map (fun z => cycleCountVector L (raceRankPermutation z)))
      (cycleVectorPoissonLaw f L)) atTop (𝓝 0) := by
  change Tendsto (fun n => cycleVectorTotalVariation
    (raceCycleVectorLaw (w n) L : Measure (Fin L → ℕ))
    (cycleVectorPoissonProbability f L : Measure (Fin L → ℕ)))
    atTop (𝓝 0)
  simp_rw [cycleVectorTotalVariation_eq_countable]
  apply CountableLaw.tendsto_probabilityTotalVariation_of_singletons
  intro q
  change Tendsto (fun n => (raceCycleVectorLaw (w n) L : Measure (Fin L → ℕ)).real {q})
    atTop (𝓝 ((cycleVectorPoissonLaw f L).real {q}))
  simp_rw [raceCycleVectorLaw_real_singleton]
  exact hend.cycle_point_probability_limit hnorm hf L q

end Luce
