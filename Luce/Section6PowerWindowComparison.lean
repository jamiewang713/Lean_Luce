import Luce.Section6Sampling

noncomputable section
namespace Luce.Section6

/-- Uniform power envelopes compare every point of a multiplicative
window to its center. This is applied to actual finite populations. -/
theorem power_window_comparison {F : ℝ → ℝ} {B r t : ℝ}
    (hB : 0 < B) (hr : r ≤ 0) (ht : 0 < t)
    (hF : ∀ s : ℝ, t/8 ≤ s → s ≤ 8*t → B*s^r/2 ≤ F s ∧ F s ≤ 2*(B*s^r)) :
    ∀ s : ℝ, t/8 ≤ s → s ≤ 8*t →
      ((8 : ℝ)^r/4)*F t ≤ F s ∧ F s ≤ (4/(8 : ℝ)^r)*F t := by
  have h8 : 0 < (8 : ℝ)^r := Real.rpow_pos_of_pos (by norm_num) _
  have hFt := hF t (by linarith) (by linarith)
  intro s hslo hshi
  have hs : 0 < s := (div_pos ht (by norm_num)).trans_le hslo
  have hFs := hF s hslo hshi
  have hpowlo := Real.rpow_le_rpow_of_nonpos hs hshi hr
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) ht.le] at hpowlo
  have hpowhi := Real.rpow_le_rpow_of_nonpos (div_pos ht (by norm_num)) hslo hr
  rw [Real.div_rpow ht.le (by norm_num : (0 : ℝ) ≤ 8)] at hpowhi
  constructor
  · calc
      _ ≤ ((8 : ℝ)^r/4)*(2*(B*t^r)) := mul_le_mul_of_nonneg_left hFt.2 (by positivity)
      _ = (B/2)*((8 : ℝ)^r*t^r) := by ring
      _ ≤ (B/2)*s^r := mul_le_mul_of_nonneg_left hpowlo (half_pos hB).le
      _ = B*s^r/2 := by ring
      _ ≤ _ := hFs.1
  · calc
      _ ≤ 2*(B*s^r) := hFs.2
      _ ≤ (2*B)*(t^r/(8 : ℝ)^r) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpowhi (by positivity : 0 ≤ 2*B)
      _ = (4/(8 : ℝ)^r)*(B*t^r/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hFt.1 (by positivity)

end Luce.Section6
