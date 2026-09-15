import Luce.Section6DeletedCountRelativeTail

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

theorem deleted_arrivals_le_beforeCount_of_lt {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) {t T : ℝ} (h : t < T) :
    (∑ i ∈ Finset.univ \ removed, clockArrivalIndicator t i old) ≤
      (deletedBeforeCount removed old T : ℝ) := by
  classical
  simp only [deletedBeforeCount, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : t < old i
  · simp only [clockArrivalIndicator, clockSurvivalIndicator, if_pos hi, sub_self]
    split_ifs <;> norm_num
  · have hT : old i < T := (le_of_not_gt hi).trans_lt h
    simp [clockArrivalIndicator, clockSurvivalIndicator, hi, hT]

/-- Late gap starts force a small arrival count. The sentinel q=0 is
handled using t>=0; ties need only the existing injective-clock event. -/
theorem deleted_gapStart_gt_imp_arrivals_le {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (hi : Function.Injective old)
    (q : Fin (Finset.univ \ removed).card) {t : ℝ} (ht : 0 ≤ t)
    (hs : t < raceGapStart (compactDeletedClocks removed old) q) :
    (∑ i ∈ Finset.univ \ removed, clockArrivalIndicator t i old) ≤ (q.val : ℝ) := by
  have hc := compactDeletedClocks_injective removed old hi
  have hb := deleted_arrivals_le_beforeCount_of_lt removed old hs
  rw [← clockBeforeCount_compactDeletedClocks] at hb
  rw [raceGapStart_eq_consecutiveGapLower _ hc] at hs hb
  unfold consecutiveGapLower at hs hb
  split_ifs at hs hb with hq
  · linarith
  · rw [clockBeforeCount_arrivalTime] at hb
    exact hb.trans (Nat.cast_le.mpr (Nat.sub_le _ _))

/-- Early-time control at a shrinking relative count scale. The numerical
mean separation premise will be supplied by the sampled-profile estimates. -/
theorem deleted_gap_start_relative_early_arrival {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card)
    {t eps : ℝ} (ht : 0 ≤ t) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hmean : (1+eps)*((n : ℝ)*deletedG w removed t) ≤ (q.val : ℝ)) :
    (exponentialRace w).real {old | raceGapStart (compactDeletedClocks removed old) q < t} ≤
      Real.exp (-eps^2*((n : ℝ)*deletedG w removed t)/4) := by
  apply le_trans _ (deleted_arrival_relative_tails w hn removed ht heps heps1).1
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [exponentialRace_injective_ae w] with old hi
  intro hs
  have hb := gapStart_lt_imp_beforeCount (compactDeletedClocks removed old)
    (compactDeletedClocks_injective removed old hi) q hs
  rw [clockBeforeCount_compactDeletedClocks] at hb
  exact hmean.trans ((Nat.cast_le.mpr hb).trans (deleted_beforeCount_le_arrivals removed old t))

/-- Late-time control with no extra stochastic input. -/
theorem deleted_gap_start_relative_late_arrival {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card)
    {t eps : ℝ} (ht : 0 ≤ t) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hmean : (q.val : ℝ) ≤ (1-eps)*((n : ℝ)*deletedG w removed t)) :
    (exponentialRace w).real {old | t < raceGapStart (compactDeletedClocks removed old) q} ≤
      Real.exp (-eps^2*((n : ℝ)*deletedG w removed t)/4) := by
  apply le_trans _ (deleted_arrival_relative_tails w hn removed ht heps heps1).2
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [exponentialRace_injective_ae w] with old hi
  intro hs
  exact (deleted_gapStart_gt_imp_arrivals_le removed old hi q ht hs).trans hmean

theorem deleted_arrivals_add_survivors {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (t : ℝ) :
    (∑ i ∈ Finset.univ \ removed, clockArrivalIndicator t i old) +
      (∑ i ∈ Finset.univ \ removed, clockSurvivalIndicator t i old) =
      ((Finset.univ \ removed).card : ℝ) := by
  simp [clockArrivalIndicator, Finset.sum_sub_distrib]

/-- Early gap starts force a survivor deficit. This form retains the
right-endpoint survivor mean rather than the much larger arrival mean. -/
theorem deleted_gap_start_relative_early_survivor {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card)
    {t eps : ℝ} (ht : 0 ≤ t) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hmean : ((Finset.univ \ removed).card : ℝ)-(q.val : ℝ) ≤
      (1-eps)*((n : ℝ)*deletedH w removed t)) :
    (exponentialRace w).real {old | raceGapStart (compactDeletedClocks removed old) q < t} ≤
      Real.exp (-eps^2*((n : ℝ)*deletedH w removed t)/4) := by
  apply le_trans _ (deleted_survivor_relative_tails w hn removed ht heps heps1).2
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [exponentialRace_injective_ae w] with old hi
  intro hs
  have hb := gapStart_lt_imp_beforeCount (compactDeletedClocks removed old)
    (compactDeletedClocks_injective removed old hi) q hs
  rw [clockBeforeCount_compactDeletedClocks] at hb
  have hbR : (q.val : ℝ) ≤ (deletedBeforeCount removed old t : ℝ) := Nat.cast_le.mpr hb
  have hc := deleted_beforeCount_add_survivors_le removed old t
  change (∑ i ∈ Finset.univ \ removed, clockSurvivalIndicator t i old) ≤ _
  linarith only [hbR, hc, hmean]

/-- Late gap starts force a survivor excess, with exact undeleted cardinality. -/
theorem deleted_gap_start_relative_late_survivor {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card)
    {t eps : ℝ} (ht : 0 ≤ t) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hmean : (1+eps)*((n : ℝ)*deletedH w removed t) ≤
      ((Finset.univ \ removed).card : ℝ)-(q.val : ℝ)) :
    (exponentialRace w).real {old | t < raceGapStart (compactDeletedClocks removed old) q} ≤
      Real.exp (-eps^2*((n : ℝ)*deletedH w removed t)/4) := by
  apply le_trans _ (deleted_survivor_relative_tails w hn removed ht heps heps1).1
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [exponentialRace_injective_ae w] with old hi
  intro hs
  have hb := deleted_gapStart_gt_imp_arrivals_le removed old hi q ht hs
  have hc := deleted_arrivals_add_survivors removed old t
  change _ ≤ (∑ i ∈ Finset.univ \ removed, clockSurvivalIndicator t i old)
  linarith only [hb, hc, hmean]

end Luce.Section6
