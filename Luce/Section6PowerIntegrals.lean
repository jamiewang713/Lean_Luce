import Luce.Section6KernelPerturbation
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open Set MeasureTheory
namespace Luce.Section6

/-- Exact power-envelope integral, valid for either sign of the endpoint
power. The condition on (a+1)/p is precisely integrability at the unsuppressed end. -/
theorem integral_power_exp {a p r : ℝ} (hp : p ≠ 0) (hr : 0 < r)
    (ha : 0 < (a+1)/p) :
    (∫ s in Ioi (0 : ℝ), s^a * Real.exp (-(r*s^p))) =
      (1/r)^((a+1)/p) * Real.Gamma ((a+1)/p) / |p| := by
  let g : ℝ → ℝ := fun y => y^((a+1)/p-1) * Real.exp (-(r*y))
  have hsub := integral_comp_rpow_Ioi g hp
  have hexp : (p-1)+p*((a+1)/p-1) = a := by field_simp; ring
  have heq : (∫ s in Ioi (0 : ℝ), (|p| * s^(p-1)) • g (s^p)) =
      |p| * ∫ s in Ioi (0 : ℝ), s^a * Real.exp (-(r*s^p)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    simp only [g, smul_eq_mul]
    rw [← Real.rpow_mul hs.le]
    calc
      _ = |p| * ((s^(p-1)*s^(p*((a+1)/p-1))) * Real.exp (-(r*s^p))) := by ring
      _ = _ := by rw [← Real.rpow_add hs, hexp]
  rw [heq] at hsub
  have hg : (∫ y in Ioi (0 : ℝ), g y) =
      (1/r)^((a+1)/p) * Real.Gamma ((a+1)/p) :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  rw [hg] at hsub
  apply (eq_div_iff (abs_ne_zero.mpr hp)).mpr
  simpa only [mul_comm] using hsub

theorem integrableOn_power_exp {a p r : ℝ} (hp : p ≠ 0) (hr : 0 < r)
    (ha : 0 < (a+1)/p) :
    IntegrableOn (fun s : ℝ => s^a * Real.exp (-(r*s^p))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_power_exp hp hr ha]
  exact (div_pos (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hr) _)
    (Real.Gamma_pos_of_pos ha)) (abs_pos.mpr hp)).ne'

theorem integral_slow_survival {beta r : ℝ} (hb : 0 < beta) (hr : 0 < r) :
    (∫ s in Ioi (0 : ℝ), Real.exp (-(r*s^beta))) =
      (1/r)^(1/beta) * Real.Gamma (1+1/beta) := by
  have h := integral_power_exp (a := 0) hb.ne' hr (by positivity)
  have hGamma : Real.Gamma (1+1/beta) = (1/beta)*Real.Gamma (1/beta) := by
    rw [add_comm, Real.Gamma_add_one (by positivity : (1/beta : ℝ) ≠ 0)]
  simp only [zero_add, Real.rpow_zero, one_mul, abs_of_pos hb] at h
  rw [h, hGamma]
  ring

theorem integrableOn_slow_survival {beta r : ℝ} (hb : 0 < beta) (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => Real.exp (-(r*s^beta))) (Ioi 0) := by
  simpa only [zero_add, Real.rpow_zero, one_mul] using
    integrableOn_power_exp (a := 0) hb.ne' hr (by positivity)

end Luce.Section6
