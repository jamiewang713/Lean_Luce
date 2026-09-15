import Luce.Section6JointErrorCutoffs
import Luce.Section6RelativeProductError

noncomputable section
namespace Luce.Section6

/-- The common deterministic error at distinct source and target depths. -/
def crossDepthError (rho n a h : ℝ) : ℝ :=
  (max a h/n)^rho+1/min a h

theorem crossDepthError_nonneg {rho n a h : ℝ} (hn : 0 < n) (ha : 0 < a) (hh : 0 < h) :
    0 ≤ crossDepthError rho n a h := by unfold crossDepthError; positivity

theorem one_depth_error_le_cross {rho eta n a h : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hh : 0 < h) (hrho : 0 ≤ rho)
    (hre : rho ≤ eta) (hsmall : max a h/n ≤ 1) :
    (a/n)^eta+1/a ≤ crossDepthError rho n a h := by
  have hscale : 0 < a/n := div_pos ha hn
  have hscale1 : a/n ≤ 1 := (div_le_div_of_nonneg_right (le_max_left _ _) hn.le).trans hsmall
  have he := Real.rpow_le_rpow_of_exponent_ge hscale hscale1 hre
  apply add_le_add (he.trans (Real.rpow_le_rpow hscale.le
    (div_le_div_of_nonneg_right (le_max_left _ _) hn.le) hrho))
    (one_div_le_one_div_of_le (lt_min ha hh) (min_le_left _ _))

theorem crossDepthError_le_two {rho n a h : ℝ}
    (hn : 0 < n) (ha : 1 ≤ a) (hh : 1 ≤ h) (hrho : 0 ≤ rho)
    (hsmall : max a h/n ≤ 1) : crossDepthError rho n a h ≤ 2 := by
  have hm : 1 ≤ min a h := le_min ha hh
  have hp : (max a h/n)^rho ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by positivity) hsmall hrho
  have hi : 1/min a h ≤ 1 := (div_le_one (zero_lt_one.trans_le hm)).mpr hm
  unfold crossDepthError
  linarith only [hp, hi]

/-- Move a same-depth scale estimate to a different source using the
literal sampled-rate expansions. No uniformity of the rate ratio itself
is assumed. -/
theorem cross_depth_relative_transport {a b A B v D eps R T : ℝ}
    (hb : 0 < b) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    (hR : 0 ≤ R) (hT : 0 ≤ T) (he : 0 ≤ eps) (he2 : eps ≤ 2)
    (haerr : |a/A-1| ≤ R*eps) (hberr : |b/B-1| ≤ R*eps)
    (hsmall : R*eps ≤ 1/2) (hv : |b*v/D-1| ≤ T*eps) :
    |a*v/((A/B)*D)-1| ≤ (8*R*T+4*R+T)*eps := by
  have hr := relative_quotient_error hR hR he haerr hberr hsmall
  have hp := relative_product_error (a := 4*R) (b := T) (by positivity) hT he he2
    (by convert hr using 1 <;> ring) hv
  have hid : ((a/A)/(b/B))*(b*v/D) = a*v/((A/B)*D) := by field_simp
  simpa only [hid, show 2*(4*R)*T+4*R+T = 8*R*T+4*R+T by ring] using hp

theorem sampled_power_ratio {c n a h p : ℝ}
    (hc : 0 < c) (hn : 0 < n) (ha : 0 < a) (hh : 0 < h) :
    (c*(a/n)^p)/(c*(h/n)^p) = (a/h)^p := by
  rw [mul_div_mul_left _ _ hc.ne', ← Real.div_rpow (div_nonneg ha.le hn.le) (div_nonneg hh.le hn.le)]
  congr 1
  field_simp

theorem left_power_ratio {a h alpha : ℝ} (ha : 0 < a) (hh : 0 < h) :
    (a/h)^(-alpha) = (h/a)^alpha := by
  rw [Real.rpow_neg (div_nonneg ha.le hh.le), ← Real.inv_rpow (div_nonneg ha.le hh.le), inv_div]

end Luce.Section6
