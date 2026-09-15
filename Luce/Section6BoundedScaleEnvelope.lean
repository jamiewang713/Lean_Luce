import Luce.Section6LeftOutsideScale

noncomputable section
namespace Luce.Section6

/-- A bounded rate-time scale allows restoration of the ordinary kernel's
exponential factor at a constant cost; the scale need not be below one. -/
theorem restore_bounded_exponential {z x B : ℝ} (hz : 0 ≤ z) (hx : x ≤ B) :
    z ≤ Real.exp B*(z*Real.exp (-x)) := by
  have he : 1 ≤ Real.exp B*Real.exp (-x) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_left he hz
  simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using hh

end Luce.Section6
