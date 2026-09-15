import Luce.Section6FastWeightedIntegral

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem fast_weighted_quadrature (grid : SamplingGrid) {n : ℕ} (hn : 0 < n)
    {alpha c t : ℝ} (ha : 0 < alpha) (hc : 0 < c) (ht : 0 < t) :
    |(∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^(-alpha)))/(n : ℝ) -
      ∫ s in (0 : ℝ)..1, rateKernel t (c*s^(-alpha))| ≤
      (2*(Real.exp (-1)/t))/(n : ℝ) := by
  let R : ℝ := (c*t)^(1/alpha)
  have hRpos : 0 < R := Real.rpow_pos_of_pos (mul_pos hc ht) _
  have hR : c*R^(-alpha) = 1/t := by
    rw [Real.rpow_neg hRpos.le]
    have hRp : R^alpha = c*t := by
      dsimp [R]
      rw [one_div alpha, Real.rpow_inv_rpow (mul_pos hc ht).le ha.ne']
    rw [hRp]
    field_simp
  let q := min R 1
  have hq0 : 0 ≤ q := le_min hRpos.le zero_le_one
  have hq1 : q ≤ 1 := min_le_right _ _
  have hqR : q ≤ R := min_le_left _ _
  have hup : MonotoneOn (fun s => rateKernel t (c*s^(-alpha))) (Icc 0 q) := by
    intro x hx y hy hxy
    change rateKernel t (c*x^(-alpha)) ≤ rateKernel t (c*y^(-alpha))
    by_cases hx0 : x = 0
    · rw [hx0, Real.zero_rpow (neg_ne_zero.mpr ha.ne'), mul_zero]
      simpa only [rateKernel, zero_mul] using
        rateKernel_nonneg (mul_nonneg hc.le (Real.rpow_nonneg hy.1 (-alpha))) (t := t)
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hypos : 0 < y := hxpos.trans_le hxy
      have hxB : 1/t ≤ c*x^(-alpha) := by
        rw [← hR]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hxpos (hx.2.trans hqR) (neg_nonpos.mpr ha.le)) hc.le
      have hyB : 1/t ≤ c*y^(-alpha) := by
        rw [← hR]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hypos (hy.2.trans hqR) (neg_nonpos.mpr ha.le)) hc.le
      exact rateKernel_antitone_after_peak ht hyB hxB
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hxpos hxy (neg_nonpos.mpr ha.le)) hc.le)
  have hdown : AntitoneOn (fun s => rateKernel t (c*s^(-alpha))) (Icc q 1) := by
    intro x hx y hy hxy
    change rateKernel t (c*y^(-alpha)) ≤ rateKernel t (c*x^(-alpha))
    by_cases hR1 : R ≤ 1
    · have hq : q = R := min_eq_left hR1
      have hRx : R ≤ x := by simpa only [hq] using hx.1
      have hRy : R ≤ y := by simpa only [hq] using hy.1
      have hxB : c*x^(-alpha) ≤ 1/t := by
        rw [← hR]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hRpos hRx (neg_nonpos.mpr ha.le)) hc.le
      have hyB : c*y^(-alpha) ≤ 1/t := by
        rw [← hR]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hRpos hRy (neg_nonpos.mpr ha.le)) hc.le
      exact rateKernel_monotone_before_peak ht hyB hxB
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (hRpos.trans_le hRx) hxy
          (neg_nonpos.mpr ha.le)) hc.le)
    · have hq : q = 1 := min_eq_right (le_of_not_ge hR1)
      have hx1 : x = 1 := le_antisymm hx.2 (by simpa [hq] using hx.1)
      have hy1 : y = 1 := le_antisymm hy.2 (by simpa [hq] using hy.1)
      simp [hx1, hy1]
  have hquad := unimodal_sample_average_error grid hn hq0 hq1 hup hdown
  apply hquad.trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hmax := rateKernel_le_exp_neg_one_div (a := c*q^(-alpha)) ht
  have hz : 0 ≤ rateKernel t (c*(0 : ℝ)^(-alpha)) := rateKernel_nonneg (by positivity)
  have ho : 0 ≤ rateKernel t (c*(1 : ℝ)^(-alpha)) := rateKernel_nonneg (by positivity)
  linarith

theorem fast_weighted_prototype_error (grid : SamplingGrid) {n : ℕ} (hn : 0 < n)
    {alpha c t : ℝ} (ha : 1 < alpha) (hc : 0 < c) (ht : 0 < t) :
    |(∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^(-alpha)))/(n : ℝ) -
      (Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha-1)| ≤
      (2*(Real.exp (-1)/t))/(n : ℝ)+c/(alpha-1) := by
  have hi := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_fast_weighted_power ha hc ht) zero_le_one
  rw [integral_fast_weighted_power ha hc ht] at hi
  have hnonneg : 0 ≤ ∫ s in Ioi (1 : ℝ), rateKernel t (c*s^(-alpha)) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact rateKernel_nonneg (mul_pos hc (Real.rpow_pos_of_pos (zero_lt_one.trans hs) _)).le
  have hdiff : |(∫ s in (0 : ℝ)..1, rateKernel t (c*s^(-alpha))) -
      (Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha-1)| =
      ∫ s in Ioi (1 : ℝ), rateKernel t (c*s^(-alpha)) := by
    rw [← hi]
    simp only [sub_sub_cancel_left, abs_neg, abs_of_nonneg hnonneg]
  calc
    _ ≤ |(∑ i : Fin n, rateKernel t (c*(samplePoint grid n i)^(-alpha)))/(n : ℝ) -
        ∫ s in (0 : ℝ)..1, rateKernel t (c*s^(-alpha))| +
        |(∫ s in (0 : ℝ)..1, rateKernel t (c*s^(-alpha))) -
        (Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha-1)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (fast_weighted_quadrature grid hn (zero_lt_one.trans ha) hc ht)
      (by rw [hdiff]; exact fast_weighted_tail_bound ha hc ht)

end Luce.Section6
