import Luce.Section6InsertionExponentialMoment

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- The manuscript moderate set has x at most h when its exponent is at most
one and both depths are at least one. No rate-family restriction is involved. -/
theorem moderate_ratio_le_depth {a h x nu : ℝ} (ha : 1 ≤ a) (hh : 1 ≤ h)
    (hnu : nu ≤ 1) (hx : x ≤ (min a h)^nu) : x ≤ h := by
  have hm : 1 ≤ min a h := le_min ha hh
  calc
    x ≤ (min a h)^nu := hx
    _ ≤ (min a h)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm hnu
    _ = min a h := Real.rpow_one _
    _ ≤ h := min_le_right _ _

theorem moderate_exponential_sum_le {a h x nu d : ℝ} (ha : 1 ≤ a) (hh : 1 ≤ h)
    (hnu : nu ≤ 1) (hx : x ≤ (min a h)^nu) (hd : 0 ≤ d) :
    Real.exp (-d*x)+Real.exp (-d*h) ≤ 2*Real.exp (-d*x) := by
  have hxh := moderate_ratio_le_depth ha hh hnu hx
  have he : Real.exp (-d*h) ≤ Real.exp (-d*x) := Real.exp_le_exp.mpr (by nlinarith)
  linarith

end Luce.Section6
