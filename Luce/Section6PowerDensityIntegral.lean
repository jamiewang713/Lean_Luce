import Luce.Section6PowerIntegrals

noncomputable section
open Set MeasureTheory
namespace Luce.Section6

theorem power_density_integrable {p A d : ℝ} (hp : p ≠ 0) (hA : 0 < A) (hd : 0 < d) :
    IntegrableOn (fun x : ℝ => A*x^(p-1)*Real.exp (-(d*A*x^p))) (Ioi 0) := by
  have he : ((p-1)+1)/p = 1 := by rw [sub_add_cancel, div_self hp]
  have hi := integrableOn_power_exp (a := p-1) hp (mul_pos hd hA) (by rw [he]; norm_num)
  simpa only [IntegrableOn, mul_assoc] using hi.const_mul A

theorem integral_power_density {p A d : ℝ} (hp : p ≠ 0) (hA : 0 < A) (hd : 0 < d) :
    (∫ x in Ioi (0 : ℝ), A*x^(p-1)*Real.exp (-(d*A*x^p))) = 1/(d*|p|) := by
  have he : ((p-1)+1)/p = 1 := by rw [sub_add_cancel, div_self hp]
  have hi := integral_power_exp (a := p-1) hp (mul_pos hd hA) (by rw [he]; norm_num)
  simp only [he, Real.rpow_one, Real.Gamma_one, mul_one] at hi
  have hh := congrArg (fun z : ℝ => A*z) hi
  rw [← integral_const_mul] at hh
  simp only [mul_assoc] at hh
  simp only [mul_assoc]
  rw [hh]
  field_simp

end Luce.Section6
