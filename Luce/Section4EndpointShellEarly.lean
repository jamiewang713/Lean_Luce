import Luce.Section4EndpointCapacityAnalytic
import Luce.Section4EndpointShellBuffer

noncomputable section
namespace Luce

theorem capacity_exponent_lower {r A B : ℝ} (hr : 1 ≤ r) (hA : 4 ≤ A)
    (hB : r * A - 1 ≤ B) : r * A / 16 ≤ (B - r)^2 / (2 * B) := by
  have hra : 4 * r ≤ r * A := by nlinarith
  have hhalf : r * A / 2 ≤ B := by nlinarith
  have htwo : 2 * r ≤ B := by nlinarith
  have hp : 0 < B := by linarith
  apply (le_div_iff₀ (by positivity : 0 < 2 * B)).mpr
  nlinarith [sq_nonneg (B / 2 - r), mul_nonneg (show 0 ≤ B by linarith)
    (show 0 ≤ B - r * A / 2 by linarith)]

/-- A summable envelope in the shell index itself avoids any extra
summability assumption or a count of shell maxima. -/
theorem shell_early_envelope {r h B : ℝ} (hr : 1 ≤ r) (hh : 64 ≤ h)
    (hB : r * Real.exp h - 1 ≤ B) :
    r * Real.exp (-((B-r)^2 / (2*B))) ≤ Real.exp (1-h) := by
  have hexp := Real.add_one_le_exp h
  have hquad := Real.pow_div_factorial_le_exp h (by linarith : 0 ≤ h) 2
  norm_num at hquad
  have heh : 32 * h ≤ Real.exp h := by nlinarith
  have hA : 4 ≤ Real.exp h := by linarith
  have hc := capacity_exponent_lower hr hA hB
  have hlog := Real.add_one_le_exp r
  calc
    r * Real.exp (-((B-r)^2 / (2*B))) ≤
        Real.exp r * Real.exp (-(r * Real.exp h / 16)) :=
      mul_le_mul (by linarith) (Real.exp_le_exp.mpr (by linarith))
        (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (r - r * Real.exp h / 16) := by rw [← Real.exp_add]; congr 1
    _ ≤ Real.exp (1-h) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (show 0 ≤ r-1 by linarith)
        (show 0 ≤ Real.exp h / 16 - 1 by linarith)]

end Luce
