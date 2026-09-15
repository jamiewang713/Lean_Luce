import Luce.Section6TypicalRestrictedSums
import Luce.Section6InsertionLpEnvelope

noncomputable section
namespace Luce.Section6

/-- Make the manuscript's exponential slack explicit: both the decay
coefficient and the positive power may decrease on depths at least one. -/
theorem stretched_tail_mono {C1 C2 d1 d2 nu1 nu2 a : ℝ} (hC1 : 0 ≤ C1)
    (hC : C1 ≤ C2) (hd2 : 0 ≤ d2) (hd : d2 ≤ d1) (hnu : nu2 ≤ nu1) (ha : 1 ≤ a) :
    C1*Real.exp (-d1*a^nu1) ≤ C2*Real.exp (-d2*a^nu2) := by
  have hp := Real.rpow_le_rpow_of_exponent_le ha hnu
  have hx : d2*a^nu2 ≤ d1*a^nu1 :=
    (mul_le_mul_of_nonneg_left hp hd2).trans
      (mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (zero_le_one.trans ha) _))
  exact mul_le_mul hC (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (hC1.trans hC)

end Luce.Section6
