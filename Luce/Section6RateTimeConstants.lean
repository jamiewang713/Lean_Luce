import Luce.Section6Sampling

noncomputable section
namespace Luce.Section6

theorem right_rate_time_leading {c beta G x : ℝ}
    (hc : 0 < c) (hb : 0 < beta) (hG : 0 < G) (hx : 0 < x) :
    (c*x^beta)*((G*c^(-(1/beta)))/x)^beta = G^beta := by
  rw [Real.div_rpow (mul_pos hG (Real.rpow_pos_of_pos hc _)).le hx.le,
    Real.mul_rpow hG.le (Real.rpow_pos_of_pos hc _).le,
    ← Real.rpow_mul hc.le, show (-(1/beta))*beta = (-1 : ℝ) by field_simp,
    Real.rpow_neg_one]
  field_simp

theorem left_rate_time_leading {c alpha G x : ℝ}
    (hc : 0 < c) (ha : 0 < alpha) (hG : 0 < G) (hx : 0 < x) :
    (c*x^(-alpha))*(x/(G*c^(1/alpha)))^alpha = G^(-alpha) := by
  rw [Real.div_rpow hx.le (mul_pos hG (Real.rpow_pos_of_pos hc _)).le,
    Real.mul_rpow hG.le (Real.rpow_pos_of_pos hc _).le,
    ← Real.rpow_mul hc.le, show (1/alpha)*alpha = (1 : ℝ) by field_simp,
    Real.rpow_one, Real.rpow_neg hx.le, Real.rpow_neg hG.le]
  field_simp

end Luce.Section6
