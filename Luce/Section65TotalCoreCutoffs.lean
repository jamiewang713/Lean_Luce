import Luce.Section6FactorialCoreCutoffs

noncomputable section
namespace Luce.Section6

theorem log_population_core_upper65 {n : ℕ} (hn : 1 ≤ n)
    (hAB : idealCoreLower n ≤ idealCoreUpper n) :
    Real.log ((n : ℝ)/(idealCoreUpper n : ℝ)) ≤ 1+Real.log (idealCoreLower n : ℝ) := by
  have hA1 : (1 : ℝ) ≤ idealCoreLower n := by exact_mod_cast idealCoreLower_pos68 n
  have hA : (0 : ℝ) < idealCoreLower n := zero_lt_one.trans_le hA1
  have hB : (0 : ℝ) < idealCoreUpper n := hA.trans_le (by exact_mod_cast hAB)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : 1 ≤ (n : ℝ)/(idealCoreLower n : ℝ) :=
    hA1.trans ((show (idealCoreLower n : ℝ) ≤ idealCoreUpper n by exact_mod_cast hAB).trans (ideal_core_upper_le_div n))
  have hf := (log_floor_errors_le_one68 hx).1
  change |Real.log (idealCoreUpper n : ℝ)-Real.log ((n : ℝ)/(idealCoreLower n : ℝ))| ≤ 1 at hf
  rw [Real.log_div hn0.ne' hA.ne'] at hf
  rw [Real.log_div hn0.ne' hB.ne']
  have := (abs_le.mp hf).1
  linarith

theorem cornerDistance_le_population65 {n : ℕ} (side : Corner) (v : Fin n) : cornerDistance side v ≤ n := by
  cases side <;> dsimp [cornerDistance] <;> omega

end Luce.Section6
