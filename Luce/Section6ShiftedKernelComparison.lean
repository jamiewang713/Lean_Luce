import Luce.Section6LeftOutsideLp

noncomputable section
namespace Luce.Section6

theorem scaled_power_le_of_depth_le {q h n a : ℝ}
    (hq : 0 ≤ q) (hh : 0 ≤ h) (hn : 0 < n) (ha : 0 ≤ a) (hqh : q ≤ 2*h) :
    (q/n)^a ≤ (2 : ℝ)^a*(h/n)^a := by
  have hb := Real.rpow_le_rpow (div_nonneg hq hn.le)
    (div_le_div_of_nonneg_right hqh hn.le) ha
  have he : 2*h/n = 2*(h/n) := by ring
  simpa only [he, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (div_nonneg hh hn.le)] using hb

/-- Comparable gap depths and rate-time scales preserve the ordinary
exponential envelope, with explicit constant and exponent losses. -/
theorem shifted_exponential_kernel_bound {x y q h K : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hq : 0 < q) (hh : 0 < h) (hK : 0 < K)
    (hhq : h ≤ 2*q) (hxy : x ≤ K*y) (hyx : y ≤ K*x) :
    (x/q)*Real.exp (-x) ≤ (2*K)*(y/h)*Real.exp (-(1/K)*y) := by
  have hinv : 1/q ≤ 2/h := (div_le_div_iff₀ hq hh).mpr (by nlinarith)
  have hratio : x/q ≤ (2*K)*(y/h) := by
    calc
      x/q = x*(1/q) := by ring
      _ ≤ (K*y)*(2/h) := mul_le_mul hxy hinv (by positivity) (by positivity)
      _ = _ := by ring
  have hscale : (1/K)*y ≤ x := by
    have hb : y/K ≤ x := (div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hyx)
    simpa [div_eq_mul_inv, mul_comm] using hb
  have he : Real.exp (-x) ≤ Real.exp (-(1/K)*y) := Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul hratio he (Real.exp_pos _).le (by positivity)

end Luce.Section6
