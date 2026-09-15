import Luce.Section6ArrivalConcentration
import Luce.Section3Interior

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

theorem survival_indicator_memLp_two {n : ℕ} (w : Weights n) (t : ℝ) (i : Fin n) :
    MemLp (clockSurvivalIndicator t i) 2 (exponentialRace w) := by
  apply memLp_of_bounded (a := (0 : ℝ)) (b := 1) _
    (measurable_clockSurvivalIndicator t i).aestronglyMeasurable 2
  exact Filter.Eventually.of_forall fun old => by
    rcases clockSurvivalIndicator_zero_one t i old with h | h <;> simp [h]

theorem survival_indicator_variance_le_mean {n : ℕ} (w : Weights n) (t : ℝ) (i : Fin n) :
    variance (clockSurvivalIndicator t i) (exponentialRace w) ≤
      ∫ old, clockSurvivalIndicator t i old ∂exponentialRace w := by
  have h := variance_le_expectation_sq (survival_indicator_memLp_two w t i).aestronglyMeasurable
  have he : (clockSurvivalIndicator t i)^2 = clockSurvivalIndicator t i := by
    funext old
    rcases clockSurvivalIndicator_zero_one t i old with h | h <;> simp [h]
  rwa [he] at h

/-- The variance scale for the actual remaining weight is its finite
second rate-moment population. No normalization or uniform rate bound. -/
theorem deleted_remaining_weight_variance {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    variance (fun old => ∑ i ∈ Finset.univ \ removed,
      w.rate i * clockSurvivalIndicator t i old) (exponentialRace w) ≤
        (n : ℝ)*deletedD w removed 2 t := by
  have hind := (clockSurvivalIndicator_independent w t).comp (fun i x => w.rate i*x)
    (fun _ => measurable_const.mul measurable_id)
  have hfun : (fun old => ∑ i ∈ Finset.univ \ removed, w.rate i*clockSurvivalIndicator t i old) =
      (∑ i ∈ Finset.univ \ removed, fun old => w.rate i*clockSurvivalIndicator t i old) := by
    ext old
    simp
  rw [hfun]
  rw [IndepFun.variance_sum
    (fun i _ => (survival_indicator_memLp_two w t i).const_mul (w.rate i))
    (fun i _ j _ hij => hind.indepFun hij)]
  calc
    _ ≤ ∑ i ∈ Finset.univ \ removed,
        (w.rate i)^2 * (∫ old, clockSurvivalIndicator t i old ∂exponentialRace w) := by
      apply Finset.sum_le_sum
      intro i _
      rw [variance_const_mul]
      exact mul_le_mul_of_nonneg_left (survival_indicator_variance_le_mean w t i) (sq_nonneg _)
    _ = (n : ℝ)*deletedD w removed 2 t := by
      simp_rw [integral_clockSurvivalIndicator w t ht]
      unfold deletedD survivalKernel
      simp only [mul_comm (w.rate _) t, neg_mul]
      field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
      simp [mul_comm]

theorem deleted_remaining_weight_mean {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ old, ∑ i ∈ Finset.univ \ removed, w.rate i*clockSurvivalIndicator t i old
      ∂exponentialRace w) = (n : ℝ)*deletedD w removed 1 t := by
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_of_zero_one (exponentialRace w) (measurable_clockSurvivalIndicator t i)
      (clockSurvivalIndicator_zero_one t i)).const_mul (w.rate i))]
  simp_rw [integral_const_mul, integral_clockSurvivalIndicator w t ht]
  unfold deletedD survivalKernel
  simp only [pow_one]
  field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  simp [mul_comm]

/-- Polynomial concentration for actual deleted remaining weight.
Every integrability and independence requirement is proved from the race. -/
theorem deleted_remaining_weight_chebyshev {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) {t eps : ℝ} (ht : 0 ≤ t) (heps : 0 < eps) :
    (exponentialRace w).real {old | eps ≤ |(∑ i ∈ Finset.univ \ removed,
      w.rate i*clockSurvivalIndicator t i old)-(n : ℝ)*deletedD w removed 1 t|} ≤
        (n : ℝ)*deletedD w removed 2 t / eps^2 := by
  have hmem : MemLp (fun old => ∑ i ∈ Finset.univ \ removed,
      w.rate i*clockSurvivalIndicator t i old) 2 (exponentialRace w) := by
    apply memLp_finsetSum
    intro i _
    exact (survival_indicator_memLp_two w t i).const_mul _
  have hc := meas_ge_le_variance_div_sq hmem heps
  have hR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at hR
  rw [deleted_remaining_weight_mean w hn removed ht] at hR
  exact hR.trans (div_le_div_of_nonneg_right (deleted_remaining_weight_variance w hn removed ht)
    (sq_nonneg _))

end Luce.Section6
