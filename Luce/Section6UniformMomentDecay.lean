import Luce.Section6KernelLp

noncomputable section
namespace Luce.Section6

/-- The factorial coefficient and exponential loss can be bounded uniformly
over the manuscript's finite range of moment orders. -/
theorem uniform_moment_decay {p p0 : ℕ} (hp : 1 ≤ p) (hpp : p ≤ p0)
    {B z d x : ℝ} (hB : 0 ≤ B) (hz : 0 ≤ z) (hd : 0 ≤ d) (hx : 0 ≤ x) :
    2*(p.factorial : ℝ)*(B*z)^p*Real.exp (-d*x) ≤
      ((2*(p0.factorial : ℝ)*B)*z*Real.exp (-(d/(p0 : ℝ))*x))^p := by
  have hp0 : 0 < p0 := lt_of_lt_of_le (by omega) hpp
  have hp0R : (0 : ℝ) < p0 := Nat.cast_pos.mpr hp0
  have hppR : (p : ℝ) ≤ p0 := by exact_mod_cast hpp
  have hfact : (p.factorial : ℝ) ≤ p0.factorial := by exact_mod_cast Nat.factorial_le hpp
  have hfact1 : (1 : ℝ) ≤ p0.factorial := by exact_mod_cast Nat.factorial_pos p0
  have hC : 1 ≤ 2*(p0.factorial : ℝ) := by linarith
  have hcoeff : 2*(p.factorial : ℝ) ≤ (2*(p0.factorial : ℝ))^p :=
    (by linarith : 2*(p.factorial : ℝ) ≤ 2*(p0.factorial : ℝ)).trans
      (le_self_pow₀ hC (by omega))
  have hscale : (p : ℝ)*(d/(p0 : ℝ)) ≤ d := by
    have := mul_le_mul_of_nonneg_right hppR (div_nonneg hd hp0R.le)
    have he : (p0 : ℝ)*(d/(p0 : ℝ)) = d := by field_simp
    rwa [he] at this
  have hexp : Real.exp (-d*x) ≤ (Real.exp (-(d/(p0 : ℝ))*x))^p := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hscale hx]
  calc
    _ ≤ ((2*(p0.factorial : ℝ))^p*(B*z)^p)*(Real.exp (-(d/(p0 : ℝ))*x))^p :=
      mul_le_mul (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (mul_nonneg hB hz) p))
        hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by simp only [mul_pow]; ring

end Luce.Section6
