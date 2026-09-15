import Luce.Section6GapOffsets

noncomputable section
namespace Luce.Section6

/-- Fixed multiplicative depth changes cost only a constant in x^p/h. -/
theorem power_over_depth_comparison {x y q h p : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hq : 0 < q) (hh : 0 < h) (hp : 0 ≤ p)
    (hxy : x ≤ 2*y) (hhq : h ≤ 2*q) :
    x^p/q ≤ (2 : ℝ)^(p+1)*(y^p/h) := by
  have hb : x^p ≤ (2*y)^p := Real.rpow_le_rpow hx hxy hp
  have hn : 0 ≤ (2*y)^p := Real.rpow_nonneg (by positivity) _
  calc
    x^p/q ≤ (2*y)^p/q := div_le_div_of_nonneg_right hb hq.le
    _ ≤ 2*(2*y)^p/h := by
      apply (div_le_div_iff₀ hq hh).mpr
      nlinarith [mul_le_mul_of_nonneg_right hhq hn]
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hy,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring

theorem left_depth_factor_comparison {a q h alpha : ℝ}
    (ha : 0 < a) (hq : 0 < q) (hh : 0 < h) (hp : 0 ≤ alpha)
    (hqh : q ≤ 2*h) (hhq : h ≤ 2*q) :
    (q/a)^alpha/q ≤ (2 : ℝ)^(alpha+1)*((h/a)^alpha/h) := by
  apply power_over_depth_comparison (div_nonneg hq.le ha.le) (div_nonneg hh.le ha.le) hq hh hp _ hhq
  have hb := div_le_div_of_nonneg_right hqh ha.le
  simpa only [mul_div_assoc] using hb

theorem right_depth_factor_comparison {a m h beta : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hh : 0 < h) (hp : 0 ≤ beta)
    (hhm : h ≤ 2*m) :
    (a/m)^beta/m ≤ (2 : ℝ)^(beta+1)*((a/h)^beta/h) := by
  apply power_over_depth_comparison (div_nonneg ha.le hm.le) (div_nonneg ha.le hh.le) hm hh hp _ hhm
  rw [show 2*(a/h) = (2*a)/h by ring]
  apply (div_le_div_iff₀ hm hh).mpr
  nlinarith [mul_le_mul_of_nonneg_left hhm ha.le]

end Luce.Section6
