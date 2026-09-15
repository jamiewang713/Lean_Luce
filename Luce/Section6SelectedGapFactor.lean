import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Luce.Section6

/-- The correction caused by later marked clocks is controlled without
assuming that insertion events are independent. -/
theorem selected_gap_relative_error {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ 1-1/((1+x)*(1+x+y)) ∧
      1-1/((1+x)*(1+x+y)) ≤ 2*x+y := by
  have hp : 0 < (1+x)*(1+x+y) := mul_pos (by linarith) (by linarith)
  have hden : 1 ≤ (1+x)*(1+x+y) := by nlinarith [mul_nonneg hx hy]
  constructor
  · have ht : 1/((1+x)*(1+x+y)) ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
    linarith
  · have hu : 0 ≤ 2*x+y := by linarith
    have hv : 0 ≤ x*x+x*y := by positivity
    have huv := mul_nonneg hu hv
    have hvu : x*x+x*y ≤ (2*x+y)^2 := by nlinarith [mul_nonneg hx hy]
    apply (sub_le_iff_le_add).mpr
    have he : ((1+x)*(1+x+y)) = 1+(2*x+y)+(x*x+x*y) := by ring
    have ht : (1-(2*x+y))*((1+x)*(1+x+y)) ≤ 1 := by
      rw [he]
      nlinarith
    have ht' := (le_div_iff₀ hp).mpr ht
    linarith

/-- Exact selected-spacing rational factor and its relative error from
theta/W. Lambda is the total rate of later selected marks. -/
theorem selected_gap_factor_error {W theta Lambda : ℝ}
    (hW : 0 < W) (ht : 0 < theta) (hL : 0 ≤ Lambda) :
    0 ≤ theta/W - W*theta/((W+Lambda)*(W+Lambda+theta)) ∧
    theta/W - W*theta/((W+Lambda)*(W+Lambda+theta)) ≤
      (theta/W)*((2*Lambda+theta)/W) := by
  have hs := selected_gap_relative_error (div_nonneg hL hW.le) (div_nonneg ht.le hW.le)
  have hscale : 0 ≤ theta/W := (div_pos ht hW).le
  have he : theta/W - W*theta/((W+Lambda)*(W+Lambda+theta)) =
      (theta/W)*(1-1/((1+Lambda/W)*(1+Lambda/W+theta/W))) := by
    have hWL : W+Lambda ≠ 0 := ne_of_gt (by linarith)
    have hWLt : W+Lambda+theta ≠ 0 := ne_of_gt (by linarith)
    field_simp
    <;> ring
  rw [he]
  refine ⟨mul_nonneg hscale hs.1, ?_⟩
  have he2 : 2*(Lambda/W)+theta/W = (2*Lambda+theta)/W := by ring
  rw [he2] at hs
  exact mul_le_mul_of_nonneg_left hs.2 hscale

end Luce.Section6
