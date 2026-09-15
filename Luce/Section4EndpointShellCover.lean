import Luce.Section4EndpointShellGeometry
import Luce.Section4TailCountIndex

noncomputable section
open scoped BigOperators
namespace Luce

theorem terminalShell_cover {n J : ℕ} (hJ : 1 ≤ J) (k : Fin n)
    (hk : (J : ℝ) ≤ Real.log ((n : ℝ)/(terminalDepth k : ℝ))) :
    ∃ j ∈ Finset.range (n+1), J ≤ j ∧ k ∈ terminalShell n j := by
  let j := ⌊Real.log ((n : ℝ)/(terminalDepth k : ℝ))⌋₊
  have hJj : J ≤ j := Nat.le_floor hk
  have hm : k ∈ terminalShell n j := mem_terminalShell.mpr
    ⟨hJ.trans hJj, Nat.floor_le ((Nat.cast_nonneg J).trans hk), Nat.lt_floor_add_one _⟩
  exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le (shell_index_le_row ⟨k, hm⟩)), hJj, hm⟩

theorem spatial_tail_log_lower {n J : ℕ} (k : Fin n)
    (hn : 2 ≤ (n : ℝ)*Real.exp (-(J : ℝ)))
    (hk : (1-Real.exp (-(J : ℝ))/2)*(n : ℝ) < (k.val : ℝ)+1) :
    (J : ℝ) ≤ Real.log ((n : ℝ)/(terminalDepth k : ℝ)) := by
  have hd : (0 : ℝ) < terminalDepth k := by exact_mod_cast terminalDepth_pos k
  have hdepth : (terminalDepth k : ℝ) + ((k.val : ℝ)+1) = (n : ℝ)+1 := by
    exact_mod_cast terminalDepth_add_label k
  have hdn : (terminalDepth k : ℝ) ≤ (n : ℝ)*Real.exp (-(J : ℝ)) := by nlinarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt k.isLt
  apply (Real.le_log_iff_exp_le (div_pos hnpos hd)).mpr
  apply (le_div_iff₀ hd).mpr
  have he := mul_le_mul_of_nonneg_right hdn (Real.exp_pos (J : ℝ)).le
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at he
  simpa only [mul_comm] using he

end Luce
