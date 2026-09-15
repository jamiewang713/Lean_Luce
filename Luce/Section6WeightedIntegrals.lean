import Luce.Section6WeightedQuadrature
import Luce.Section6PowerIntegrals

noncomputable section
open Set MeasureTheory
namespace Luce.Section6

theorem rateKernel_split_time (t a : ℝ) :
    rateKernel t a = rateKernel (t/2) a * survivalKernel (t/2) a := by
  simp only [rateKernel, survivalKernel]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The nonendpoint weighted population has an exponentially small bound
without any upper bound on its rates. -/
theorem rateKernel_bound_above_lower {t a d : ℝ} (ht : 0 < t) (ha : d ≤ a) :
    rateKernel t a ≤ (Real.exp (-1)/(t/2))*survivalKernel (t/2) d := by
  rw [rateKernel_split_time]
  apply mul_le_mul (rateKernel_le_exp_neg_one_div (half_pos ht)) _
    (survivalKernel_pos _ _).le (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left ha (by linarith : -(t/2) ≤ 0)

theorem weighted_power_kernel_identity (c beta t s : ℝ) :
    rateKernel t (c*s^beta) = c*(s^beta*Real.exp (-((c*t)*s^beta))) := by
  unfold rateKernel survivalKernel
  have heq : -t*(c*s^beta) = -((c*t)*s^beta) := by ring
  rw [heq]
  ring

theorem integral_weighted_power {beta c t : ℝ} (hb : 0 < beta) (hc : 0 < c) (ht : 0 < t) :
    (∫ s in Ioi (0 : ℝ), rateKernel t (c*s^beta)) =
      c*((1/(c*t))^((beta+1)/beta)*Real.Gamma ((beta+1)/beta)/beta) := by
  simp_rw [weighted_power_kernel_identity]
  rw [integral_const_mul, integral_power_exp hb.ne' (mul_pos hc ht)
    (div_pos (by linarith) hb), abs_of_pos hb]

theorem integrableOn_weighted_power {beta c t : ℝ} (hb : 0 < beta) (hc : 0 < c) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => rateKernel t (c*s^beta)) (Ioi 0) := by
  simp_rw [weighted_power_kernel_identity]
  exact (integrableOn_power_exp hb.ne' (mul_pos hc ht) (div_pos (by linarith) hb)).const_mul c

end Luce.Section6
