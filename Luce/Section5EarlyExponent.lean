import Luce.EndpointShellEarly

noncomputable section
namespace Luce

theorem half_mean_exponent {B q : ℝ} (hB : 0 < B) (hq : 0 ≤ q) (hhalf : 2*q ≤ B) :
    B/8 ≤ (B-q)^2/(2*B) := by
  apply (le_div_iff₀ (by positivity : 0 < 2*B)).mpr
  nlinarith [sq_nonneg (B/2-q), mul_nonneg hq (show 0 ≤ B-2*q by linarith)]

/-- The finite window-width offset is absorbed by a cutoff depending only
on the fixed cycle length. The logarithmic time coefficient stays one. -/
theorem shell_early_envelope_offset {r h ell : ℝ} (hr : 1 ≤ r) (hell : 0 ≤ ell)
    (hh : 64 ≤ h) (hoff : 2*(ell+1) ≤ Real.exp h) :
    r * Real.exp (-((r*Real.exp h-(r+ell))^2/(2*(r*Real.exp h)))) ≤ Real.exp (1-h) := by
  have hp : 0 < r*Real.exp h := mul_pos (by linarith) (Real.exp_pos _)
  have hhalf : 2*(r+ell) ≤ r*Real.exp h := by
    nlinarith [mul_nonneg (show 0 ≤ r-1 by linarith)
      (show 0 ≤ Real.exp h-2 by linarith)]
  have hc := half_mean_exponent hp (show 0 ≤ r+ell by linarith) hhalf
  have hquad := Real.pow_div_factorial_le_exp h (by linarith : 0 ≤ h) 2
  norm_num at hquad
  have heh : 32*h ≤ Real.exp h := by nlinarith
  have hlog := Real.add_one_le_exp r
  calc
    _ ≤ Real.exp r * Real.exp (-(r*Real.exp h/16)) :=
      mul_le_mul (by linarith) (Real.exp_le_exp.mpr (by linarith))
        (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (r-r*Real.exp h/16) := by rw [← Real.exp_add]; congr 1
    _ ≤ Real.exp (1-h) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (show 0 ≤ r-1 by linarith)
        (show 0 ≤ Real.exp h/16-1 by linarith)]

end Luce
