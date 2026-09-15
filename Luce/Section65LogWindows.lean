import Luce.Section6IdealSpatialWindow
import Luce.Section6LogExcursionAlgebra

noncomputable section
open Filter
namespace Luce.Section6

theorem logLocation_window_iff65 {n : ℕ} (hn : 2 ≤ n) (side : Corner)
    (v : Fin n) (a b : ℝ) :
    (a < logLocation side v ∧ logLocation side v ≤ b) ↔
      (n : ℝ)^a < (cornerDistance side v : ℝ) ∧ (cornerDistance side v : ℝ) ≤ (n : ℝ)^b := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hv : (0 : ℝ) < cornerDistance side v := by exact_mod_cast cornerDistance_pos67 side v
  unfold logLocation
  rw [lt_div_iff₀ hl,div_le_iff₀ hl]
  rw [← Real.log_rpow hn0,← Real.log_rpow hn0]
  exact and_congr (Real.log_lt_log_iff (Real.rpow_pos_of_pos hn0 a) hv)
    (Real.log_le_log_iff hv (Real.rpow_pos_of_pos hn0 b))

theorem power_window_inside_core65 {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (n : ℝ)^a < (m : ℝ) → (m : ℝ) ≤ (n : ℝ)^b →
      idealCoreLower n ≤ m ∧ m ≤ idealCoreUpper n := by
  filter_upwards [idealSpatialWindow68_eventually ha hab hb (show (0 : ℝ) < 1 by norm_num)] with n hw
  intro m hmA hmB
  have hA := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) a)
  have hAm : ⌊(n : ℝ)^a⌋₊ ≤ m := by exact_mod_cast hA.trans hmA.le
  have hmQ : m ≤ ⌊(n : ℝ)^b⌋₊ := (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg n) b)).mpr hmB
  exact ⟨hw.lower_le.trans hAm,hmQ.trans (Nat.le_succ _ |>.trans hw.upper_le)⟩

end Luce.Section6
