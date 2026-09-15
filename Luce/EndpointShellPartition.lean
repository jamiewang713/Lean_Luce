import Luce.EndpointShellTailBridge

/-! Exact weighted partition of terminal depths by logarithmic shells. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Luce

def terminalDepthBlock (n J : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun k => (terminalDepth k : ℝ) ≤ (n : ℝ) * Real.exp (-(J : ℝ))

theorem terminalDepth_le_iff_log {n J : ℕ} (k : Fin n) :
    (terminalDepth k : ℝ) ≤ (n : ℝ) * Real.exp (-(J : ℝ)) ↔
      (J : ℝ) ≤ Real.log ((n : ℝ) / (terminalDepth k : ℝ)) := by
  have hd : (0 : ℝ) < terminalDepth k := by exact_mod_cast terminalDepth_pos k
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt k.isLt
  rw [Real.le_log_iff_exp_le (div_pos hn hd), le_div_iff₀ hd, Real.exp_neg]
  rw [← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  rw [mul_comm (terminalDepth k : ℝ)]

theorem terminalShell_index_unique {n a b : ℕ} {k : Fin n}
    (ha : k ∈ terminalShell n a) (hb : k ∈ terminalShell n b) : a = b := by
  have ha' := (mem_terminalShell.mp ha).2
  have hb' := (mem_terminalShell.mp hb).2
  have hab : (a : ℝ) < (b : ℝ) + 1 := ha'.1.trans_lt hb'.2
  have hba : (b : ℝ) < (a : ℝ) + 1 := hb'.1.trans_lt ha'.2
  have hab' : a < b + 1 := by exact_mod_cast hab
  have hba' : b < a + 1 := by exact_mod_cast hba
  omega

theorem terminalDepthBlock_sum_eq_shells {n J : ℕ} (hJ : 1 ≤ J)
    (p : Fin n → ℝ≥0∞) :
    (∑ k ∈ terminalDepthBlock n J, p k) =
      ∑' j : ℕ, if J ≤ j then ∑ k ∈ terminalShell n j, p k else 0 := by
  classical
  have hs : (∑' j : ℕ, if J ≤ j then ∑ k ∈ terminalShell n j, p k else 0) =
      ∑ j ∈ Finset.range (n+1), if J ≤ j then ∑ k ∈ terminalShell n j, p k else 0 := by
    apply tsum_eq_sum
    intro j hj
    have he : terminalShell n j = ∅ := Finset.not_nonempty_iff_eq_empty.mp
      (fun hh => (not_lt_of_ge (shell_index_le_row hh))
        (by simp only [Finset.mem_range] at hj; omega))
    simp [he]
  rw [hs]
  have he : (∑ j ∈ Finset.range (n+1), if J ≤ j then ∑ k ∈ terminalShell n j, p k else 0) =
      ∑ k : Fin n, ∑ j ∈ Finset.range (n+1),
        if J ≤ j ∧ k ∈ terminalShell n j then p k else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : J ≤ j <;> simp [hj, terminalShell, Finset.sum_filter]
  rw [he]
  simp only [terminalDepthBlock, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (terminalDepth k : ℝ) ≤ (n : ℝ) * Real.exp (-(J : ℝ))
  · rw [if_pos hk]
    obtain ⟨j, hj, hJj, hkj⟩ := terminalShell_cover hJ k ((terminalDepth_le_iff_log k).mp hk)
    symm
    rw [Finset.sum_eq_single_of_mem j hj]
    · simp [hJj, hkj]
    · intro b _ hbj
      by_cases hb : J ≤ b ∧ k ∈ terminalShell n b
      · exact False.elim (hbj (terminalShell_index_unique hb.2 hkj))
      · simp [hb]
  · rw [if_neg hk]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hj : ¬ (J ≤ j ∧ k ∈ terminalShell n j) := by
      rintro ⟨hJj, hkj⟩
      apply hk
      apply (terminalDepth_le_iff_log k).mpr
      exact (Nat.cast_le.mpr hJj).trans (mem_terminalShell.mp hkj).2.1
    simp [hj]

end Luce
