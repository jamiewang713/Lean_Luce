import Luce.Section6ComparableDepthPowers

noncomputable section
namespace Luce.Section6

/-- Weighted powers at a discrete depth compared to its following unit cell.
Only the comparison envelope's decay constant is reduced. -/
theorem power_weighted_cell_bound {h x A d : ℝ} (hh : 1 ≤ h)
    (hx : h ≤ x) (hxh : x ≤ h+1) (hA : 0 < A) (hd : 0 < d) (p a : ℝ) :
    A*h^a*Real.exp (-(d*A*h^p)) ≤
      (2 : ℝ)^|a| * (A*x^a*Real.exp (-((d/(2 : ℝ)^|p|)*A*x^p))) := by
  have hh0 : 0 < h := zero_lt_one.trans_le hh
  have hx0 : 0 < x := hh0.trans_le hx
  have hx2 : x ≤ 2*h := by linarith
  have hpref := (comparable_depth_rpow_bounds hh0 hx hx2 a).1
  have hscale := (comparable_depth_rpow_bounds hh0 hx hx2 p).2
  have hR : (0 : ℝ) < (2 : ℝ)^|p| := by positivity
  have he : (d/(2 : ℝ)^|p|)*A*x^p ≤ d*A*h^p := by
    have hb := mul_le_mul_of_nonneg_left hscale (show 0 ≤ (d/(2 : ℝ)^|p|)*A by positivity)
    have hid : ((d/(2 : ℝ)^|p|)*A)*((2 : ℝ)^|p| * h^p) = d*A*h^p := by field_simp
    simpa only [hid, mul_assoc] using hb
  have hex := Real.exp_le_exp.mpr (neg_le_neg he)
  have hprefA := mul_le_mul_of_nonneg_left hpref hA.le
  have hb := mul_le_mul hprefA hex (Real.exp_pos _).le (by positivity)
  nlinarith only [hb]

end Luce.Section6
