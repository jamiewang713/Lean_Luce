import Luce.Section6FastArrivalIntegral
import Luce.Section6MonotoneQuadrature

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

/-- Both-grid quadrature for the fast-arrival prototype. The auxiliary
value 1 at zero is used only for monotone quadrature; equality of the
original integral and all sampled values is proved explicitly. -/
theorem fast_arrival_quadrature (grid : SamplingGrid) {n : ℕ} (hn : 0 < n)
    {alpha r : ℝ} (ha : 0 < alpha) (hr : 0 < r) :
    |(∑ i : Fin n, (1-Real.exp (-(r*(samplePoint grid n i)^(-alpha)))))/(n : ℝ) -
      ∫ s in (0 : ℝ)..1, 1-Real.exp (-(r*s^(-alpha)))| ≤ 1/(n : ℝ) := by
  let g : ℝ → ℝ := fun s => if s = 0 then 1 else 1-Real.exp (-(r*s^(-alpha)))
  have hg : AntitoneOn g (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    by_cases hx0 : x = 0
    · by_cases hy0 : y = 0
      · simp [g, hx0, hy0]
      · have hh := one_sub_exp_neg_bounds (mul_nonneg hr.le (Real.rpow_nonneg hy.1 (-alpha)))
        simpa only [g, hx0, if_pos rfl, if_neg hy0] using hh.2.1
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hypos : 0 < y := hxpos.trans_le hxy
      simp only [g, if_neg hx0, if_neg hypos.ne']
      apply sub_le_sub_left
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hxpos hxy (neg_nonpos.mpr ha.le)) hr.le)
  have hquad := antitone_sample_average_error grid hn hg
  have hsample : (∑ i : Fin n, g (samplePoint grid n i)) =
      ∑ i : Fin n, (1-Real.exp (-(r*(samplePoint grid n i)^(-alpha)))) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [g, if_neg (samplePoint_mem grid i).1.ne']
  have hint : (∫ s in (0 : ℝ)..1, g s) =
      ∫ s in (0 : ℝ)..1, 1-Real.exp (-(r*s^(-alpha))) := by
    apply intervalIntegral.integral_congr_uIoo
    intro s hs
    have hs' : s ∈ Ioo (0 : ℝ) 1 := by simpa using hs
    simp only [g, if_neg hs'.1.ne']
  rw [hsample, hint] at hquad
  have hdrop : g 0-g 1 ≤ 1 := by
    have hh := one_sub_exp_neg_bounds hr.le
    simp only [g, if_pos rfl, if_neg (one_ne_zero : (1 : ℝ) ≠ 0), Real.one_rpow, mul_one]
    linarith
  exact hquad.trans (div_le_div_of_nonneg_right hdrop (Nat.cast_nonneg n))

theorem fast_arrival_tail_bound {alpha r : ℝ} (ha : 1 < alpha) (hr : 0 < r) :
    (∫ s in Ioi (1 : ℝ), 1-Real.exp (-(r*s^(-alpha)))) ≤ r/(alpha-1) := by
  have hi := (integrableOn_fast_arrival ha hr).mono_set (Ioi_subset_Ioi zero_le_one)
  have hp := (integrableOn_Ioi_rpow_of_lt (by linarith : -alpha < -1) zero_lt_one).const_mul r
  calc
    _ ≤ ∫ s in Ioi (1 : ℝ), r*s^(-alpha) := by
      apply setIntegral_mono_on hi hp measurableSet_Ioi
      intro s hs
      exact (one_sub_exp_neg_bounds (mul_pos hr
        (Real.rpow_pos_of_pos (zero_lt_one.trans hs) (-alpha))).le).2.2
    _ = r/(alpha-1) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -alpha < -1) zero_lt_one,
        Real.one_rpow]
      rw [show -alpha+1 = -(alpha-1) by ring, div_neg, neg_div, neg_neg]
      ring

theorem fast_arrival_prototype_error (grid : SamplingGrid) {n : ℕ} (hn : 0 < n)
    {alpha r : ℝ} (ha : 1 < alpha) (hr : 0 < r) :
    |(∑ i : Fin n, (1-Real.exp (-(r*(samplePoint grid n i)^(-alpha)))))/(n : ℝ) -
      r^(1/alpha)*Real.Gamma (1-1/alpha)| ≤ 1/(n : ℝ)+r/(alpha-1) := by
  have hi := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_fast_arrival ha hr) zero_le_one
  rw [integral_fast_arrival ha hr] at hi
  have hnonneg : 0 ≤ ∫ s in Ioi (1 : ℝ), 1-Real.exp (-(r*s^(-alpha))) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (one_sub_exp_neg_bounds (mul_pos hr
      (Real.rpow_pos_of_pos (zero_lt_one.trans hs) (-alpha))).le).1
  have hdiff : |(∫ s in (0 : ℝ)..1, 1-Real.exp (-(r*s^(-alpha)))) -
      r^(1/alpha)*Real.Gamma (1-1/alpha)| =
      ∫ s in Ioi (1 : ℝ), 1-Real.exp (-(r*s^(-alpha))) := by
    rw [← hi]
    simp only [sub_sub_cancel_left, abs_neg, abs_of_nonneg hnonneg]
  calc
    _ ≤ |(∑ i : Fin n, (1-Real.exp (-(r*(samplePoint grid n i)^(-alpha)))))/(n : ℝ) -
        ∫ s in (0 : ℝ)..1, 1-Real.exp (-(r*s^(-alpha)))| +
        |(∫ s in (0 : ℝ)..1, 1-Real.exp (-(r*s^(-alpha)))) -
        r^(1/alpha)*Real.Gamma (1-1/alpha)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (fast_arrival_quadrature grid hn (zero_lt_one.trans ha) hr)
      (by rw [hdiff]; exact fast_arrival_tail_bound ha hr)

end Luce.Section6
