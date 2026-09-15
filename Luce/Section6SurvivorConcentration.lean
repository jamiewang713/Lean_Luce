import Luce.Section6GapStartTail

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Strict arrivals and strict survivors are disjoint, including at ties.
The original undeleted label set is used on both sides. -/
theorem deleted_beforeCount_add_survivors_le {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (t : ℝ) :
    (deletedBeforeCount removed old t : ℝ)+
      (∑ i ∈ Finset.univ \ removed, clockSurvivalIndicator t i old) ≤
      ((Finset.univ \ removed).card : ℝ) := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ \ removed,
        ((if old i < t then (1 : ℝ) else 0)+clockSurvivalIndicator t i old) := by
      simp only [deletedBeforeCount, Finset.card_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_add_distrib]
    _ ≤ ∑ _i ∈ Finset.univ \ removed, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : old i < t
      · simp [hi, clockSurvivalIndicator, not_lt.mpr hi.le]
      · simp only [if_neg hi, zero_add, clockSurvivalIndicator]
        split_ifs <;> norm_num
    _ = _ := by simp

theorem deleted_survivor_mean_identity {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    (∑ i ∈ Finset.univ \ removed, ∫ old, clockSurvivalIndicator t i old ∂exponentialRace w) =
      (n : ℝ)*deletedH w removed t := by
  simp_rw [integral_clockSurvivalIndicator w t ht]
  unfold deletedH survivalKernel
  simp only [mul_comm (w.rate _) t, neg_mul]
  field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]

/-- Finite right-tail helper: an early gap start forces a survivor lower
tail. The mean premise is explicit and still requires endpoint discharge. -/
theorem deleted_gap_start_tail_of_survivor_mean {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card)
    {t : ℝ} (ht : 0 ≤ t)
    (hmean : 2*(((Finset.univ \ removed).card : ℝ)-(q.val : ℝ)) ≤ (n : ℝ)*deletedH w removed t) :
    (exponentialRace w).real {old | raceGapStart (compactDeletedClocks removed old) q < t} ≤
      Real.exp (-2*bernoulliLowerTailConstant*
        (((Finset.univ \ removed).card : ℝ)-(q.val : ℝ))) := by
  have hb := bernoulli_sum_lower_tail (exponentialRace w) (clockSurvivalIndicator t)
    (measurable_clockSurvivalIndicator t) (clockSurvivalIndicator_zero_one t)
    (clockSurvivalIndicator_independent w t) (Finset.univ \ removed)
  rw [deleted_survivor_mean_identity w hn removed ht] at hb
  apply le_trans _ (hb.trans _)
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
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
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hmean bernoulliLowerTailConstant_pos.le]

end Luce.Section6
