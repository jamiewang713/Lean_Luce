import Luce.Section6FastArrivalIntegral
import Luce.Section6PopulationPowerBounds

noncomputable section
open Set MeasureTheory
namespace Luce.Section6

theorem integral_fast_weighted_power {alpha c t : ℝ}
    (ha : 1 < alpha) (hc : 0 < c) (ht : 0 < t) :
    (∫ s in Ioi (0 : ℝ), rateKernel t (c*s^(-alpha))) =
      (Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha-1) := by
  have ha0 : 0 < alpha := zero_lt_one.trans ha
  have hexp : (-alpha+1)/(-alpha) = 1-1/alpha := by field_simp; ring
  simp_rw [weighted_power_kernel_identity]
  rw [integral_const_mul, integral_power_exp (neg_ne_zero.mpr ha0.ne') (mul_pos hc ht)
    (div_pos_of_neg_of_neg (by linarith) (by linarith)), abs_neg, abs_of_pos ha0,
    hexp, reciprocal_scaled_rpow hc ht]
  have hcp : c*c^(-(1-1/alpha)) = c^(1/alpha) := by
    conv_lhs => lhs; rw [← Real.rpow_one c]
    rw [← Real.rpow_add hc]
    congr 1
    ring
  have htp : -(1-1/alpha) = 1/alpha-1 := by ring
  rw [htp]
  calc
    _ = (Real.Gamma (1-1/alpha)*(c*c^(-(1-1/alpha)))/alpha)*t^(1/alpha-1) := by
      rw [htp]
      ring
    _ = _ := by rw [hcp]

theorem integrableOn_fast_weighted_power {alpha c t : ℝ}
    (ha : 1 < alpha) (hc : 0 < c) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => rateKernel t (c*s^(-alpha))) (Ioi 0) := by
  simp_rw [weighted_power_kernel_identity]
  exact (integrableOn_power_exp (neg_ne_zero.mpr (zero_lt_one.trans ha).ne') (mul_pos hc ht)
    (div_pos_of_neg_of_neg (by linarith : -alpha+1 < 0) (by linarith))).const_mul c

theorem fast_weighted_tail_bound {alpha c t : ℝ}
    (ha : 1 < alpha) (hc : 0 < c) (ht : 0 < t) :
    (∫ s in Ioi (1 : ℝ), rateKernel t (c*s^(-alpha))) ≤ c/(alpha-1) := by
  have hi := (integrableOn_fast_weighted_power ha hc ht).mono_set (Ioi_subset_Ioi zero_le_one)
  have hp := (integrableOn_Ioi_rpow_of_lt (by linarith : -alpha < -1) zero_lt_one).const_mul c
  calc
    _ ≤ ∫ s in Ioi (1 : ℝ), c*s^(-alpha) := by
      apply setIntegral_mono_on hi hp measurableSet_Ioi
      intro s hs
      have hrate : 0 ≤ c*s^(-alpha) := (mul_pos hc (Real.rpow_pos_of_pos (zero_lt_one.trans hs) _)).le
      simpa only [rateKernel, mul_one] using
        mul_le_mul_of_nonneg_left (survivalKernel_le_one ht.le hrate) hrate
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -alpha < -1) zero_lt_one,
        Real.one_rpow, show -alpha+1 = -(alpha-1) by ring, div_neg, neg_div, neg_neg]
      ring

end Luce.Section6
