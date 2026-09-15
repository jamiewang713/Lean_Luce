import Luce.Section6PowerIntegrals

noncomputable section
open Set MeasureTheory
namespace Luce.Section6

theorem power_weighted_density_integrable {a p A d : ℝ}
    (hp : p ≠ 0) (hq : 0 < (a+1)/p) (hA : 0 < A) (hd : 0 < d) :
    IntegrableOn (fun x : ℝ => A*x^a*Real.exp (-(d*A*x^p))) (Ioi 0) := by
  simpa only [IntegrableOn, mul_assoc] using
    (integrableOn_power_exp hp (mul_pos hd hA) hq).const_mul A

theorem integral_power_weighted_density {a p A d : ℝ}
    (hp : p ≠ 0) (hq : 0 < (a+1)/p) (hA : 0 < A) (hd : 0 < d) :
    (∫ x in Ioi (0 : ℝ), A*x^a*Real.exp (-(d*A*x^p))) =
      ((1/d)^((a+1)/p)*Real.Gamma ((a+1)/p)/|p|)*A^(1-(a+1)/p) := by
  have hi := integral_power_exp hp (mul_pos hd hA) hq
  have hh := congrArg (fun z : ℝ => A*z) hi
  rw [← integral_const_mul] at hh
  simp only [mul_assoc] at hh ⊢
  rw [hh]
  have hrec : 1/(d*A) = (1/d)*(1/A) := by field_simp
  rw [hrec, Real.mul_rpow (by positivity : 0 ≤ 1/d) (by positivity : 0 ≤ 1/A)]
  have hscale : A*(1/A)^((a+1)/p) = A^(1-(a+1)/p) := by
    rw [Real.div_rpow zero_le_one hA.le, Real.one_rpow, Real.rpow_sub hA, Real.rpow_one]
    ring
  calc
    _ = ((1/d)^((a+1)/p)*Real.Gamma ((a+1)/p)/|p|)*(A*(1/A)^((a+1)/p)) := by ring
    _ = _ := by rw [hscale]

end Luce.Section6
