import Luce.Section6BernoulliRelativeTail
import Luce.Section6ArrivalConcentration
import Luce.Section6SurvivorConcentration

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Shrinking-scale concentration for actual deleted arrival counts.
The mean is the manuscript's finite deleted population, not an input bound. -/
theorem deleted_arrival_relative_tails {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) {t eps : ℝ} (ht : 0 ≤ t)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) :
    (exponentialRace w).real {old | (1+eps)*((n : ℝ)*deletedG w removed t) ≤
      ∑ i ∈ Finset.univ \ removed, clockArrivalIndicator t i old} ≤
        Real.exp (-eps^2*((n : ℝ)*deletedG w removed t)/4) ∧
    (exponentialRace w).real {old | (∑ i ∈ Finset.univ \ removed, clockArrivalIndicator t i old) ≤
      (1-eps)*((n : ℝ)*deletedG w removed t)} ≤
        Real.exp (-eps^2*((n : ℝ)*deletedG w removed t)/4) := by
  have hm : (∑ i ∈ Finset.univ \ removed, ∫ old, clockArrivalIndicator t i old ∂exponentialRace w) =
      (n : ℝ)*deletedG w removed t := by
    simp_rw [integral_clockArrivalIndicator w t ht]
    unfold deletedG
    field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  have hu := bernoulli_relative_upper_tail (exponentialRace w) (clockArrivalIndicator t)
    (measurable_clockArrivalIndicator t) (clockArrivalIndicator_zero_one t)
    (clockArrivalIndicator_independent w t) (Finset.univ \ removed) heps heps1
  have hl := bernoulli_relative_lower_tail (exponentialRace w) (clockArrivalIndicator t)
    (measurable_clockArrivalIndicator t) (clockArrivalIndicator_zero_one t)
    (clockArrivalIndicator_independent w t) (Finset.univ \ removed) heps heps1
  dsimp only at hu hl
  rw [hm] at hu hl
  exact ⟨hu, hl⟩

/-- Shrinking-scale concentration for actual deleted survivors, with all
independence, mean, and exponential-integrability premises discharged. -/
theorem deleted_survivor_relative_tails {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) {t eps : ℝ} (ht : 0 ≤ t)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) :
    (exponentialRace w).real {old | (1+eps)*((n : ℝ)*deletedH w removed t) ≤
      ∑ i ∈ Finset.univ \ removed, clockSurvivalIndicator t i old} ≤
        Real.exp (-eps^2*((n : ℝ)*deletedH w removed t)/4) ∧
    (exponentialRace w).real {old | (∑ i ∈ Finset.univ \ removed, clockSurvivalIndicator t i old) ≤
      (1-eps)*((n : ℝ)*deletedH w removed t)} ≤
        Real.exp (-eps^2*((n : ℝ)*deletedH w removed t)/4) := by
  have hu := bernoulli_relative_upper_tail (exponentialRace w) (clockSurvivalIndicator t)
    (measurable_clockSurvivalIndicator t) (clockSurvivalIndicator_zero_one t)
    (clockSurvivalIndicator_independent w t) (Finset.univ \ removed) heps heps1
  have hl := bernoulli_relative_lower_tail (exponentialRace w) (clockSurvivalIndicator t)
    (measurable_clockSurvivalIndicator t) (clockSurvivalIndicator_zero_one t)
    (clockSurvivalIndicator_independent w t) (Finset.univ \ removed) heps heps1
  dsimp only at hu hl
  rw [deleted_survivor_mean_identity w hn removed ht] at hu hl
  exact ⟨hu, hl⟩

end Luce.Section6
