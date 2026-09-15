import Luce.Section6SurvivorConcentration

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Retain decay in the full survivor mean, which can be much larger than
the demanded terminal depth in the right extreme regime. -/
theorem deleted_gap_start_tail_of_survivor_mean_sharp {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card)
    {t : ℝ} (ht : 0 ≤ t)
    (hmean : 2*(((Finset.univ \ removed).card : ℝ)-(q.val : ℝ)) ≤ (n : ℝ)*deletedH w removed t) :
    (exponentialRace w).real {old | raceGapStart (compactDeletedClocks removed old) q < t} ≤
      Real.exp (-bernoulliLowerTailConstant*((n : ℝ)*deletedH w removed t)) := by
  have hb := bernoulli_sum_lower_tail (exponentialRace w) (clockSurvivalIndicator t)
    (measurable_clockSurvivalIndicator t) (clockSurvivalIndicator_zero_one t)
    (clockSurvivalIndicator_independent w t) (Finset.univ \ removed)
  rw [deleted_survivor_mean_identity w hn removed ht] at hb
  apply le_trans _ hb
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [exponentialRace_injective_ae w] with old hi
  intro hs
  have hq := gapStart_lt_imp_beforeCount (compactDeletedClocks removed old)
    (compactDeletedClocks_injective removed old hi) q hs
  rw [clockBeforeCount_compactDeletedClocks] at hq
  have hqR : (q.val : ℝ) ≤ (deletedBeforeCount removed old t : ℝ) := Nat.cast_le.mpr hq
  have hc := deleted_beforeCount_add_survivors_le removed old t
  change (∑ i ∈ Finset.univ \ removed, clockSurvivalIndicator t i old) ≤
    (n : ℝ)*deletedH w removed t/2
  linarith

end Luce.Section6
