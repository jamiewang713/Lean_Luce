import Luce.Section6LeftExtremeLp
import Luce.Section6RightExtremeLp
import Luce.Section6ModerateInsertionLp

noncomputable section
namespace Luce.Section6

theorem insertion_envelope_mono {C1 C2 d1 d2 z x : ℝ} (hC1 : 0 ≤ C1)
    (hC : C1 ≤ C2) (hd : d2 ≤ d1) (hz : 0 ≤ z) (hx : 0 ≤ x) :
    C1*z*Real.exp (-d1*x) ≤ C2*z*Real.exp (-d2*x) := by
  apply mul_le_mul (mul_le_mul_of_nonneg_right hC hz)
    (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
  exact mul_nonneg (hC1.trans hC) hz

end Luce.Section6
