import Luce.Section4EndpointShells

noncomputable section
open scoped BigOperators
namespace Luce

def shellMax (n j : ℕ) (h : (terminalShell n j).Nonempty) : ℕ :=
  ((terminalShell n j).image terminalDepth).max' (h.image _)

theorem shellMax_attained (n j : ℕ) (h : (terminalShell n j).Nonempty) :
    ∃ k ∈ terminalShell n j, terminalDepth k = shellMax n j h := by
  classical
  exact Finset.mem_image.mp (Finset.max'_mem _ (h.image _))

theorem shellMax_pos (n j : ℕ) (h : (terminalShell n j).Nonempty) :
    0 < shellMax n j h := by
  obtain ⟨k, _, hk⟩ := shellMax_attained n j h
  rw [← hk]
  exact terminalDepth_pos k

theorem shellMax_log (n j : ℕ) (h : (terminalShell n j).Nonempty) :
    (j : ℝ) ≤ Real.log ((n : ℝ) / shellMax n j h) := by
  obtain ⟨k, hk, heq⟩ := shellMax_attained n j h
  rw [← heq]
  exact (mem_terminalShell.mp hk).2.1

theorem shell_card_le_max (n j : ℕ) (h : (terminalShell n j).Nonempty) :
    (terminalShell n j).card ≤ shellMax n j h := by
  classical
  have hinj := Finset.card_image_of_injective (terminalShell n j) (terminalDepth_injective n)
  calc
    _ = ((terminalShell n j).image terminalDepth).card := hinj.symm
    _ ≤ (Finset.Icc 1 (shellMax n j h)).card := Finset.card_le_card (by
      intro m hm
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_Icc.mpr ⟨terminalDepth_pos k,
        Finset.le_max' _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)⟩)
    _ = shellMax n j h := by simp

theorem shellMax_exp_le (n j : ℕ) (h : (terminalShell n j).Nonempty) :
    (shellMax n j h : ℝ) * Real.exp (j : ℝ) ≤ n := by
  have hr : (0 : ℝ) < shellMax n j h := by exact_mod_cast shellMax_pos n j h
  have hn : (0 : ℝ) < n := by
    obtain ⟨k, _⟩ := h
    exact_mod_cast Nat.zero_lt_of_lt k.isLt
  have he := Real.exp_le_exp.mpr (shellMax_log n j h)
  rw [Real.exp_log (div_pos hn hr)] at he
  simpa only [mul_comm] using (le_div_iff₀ hr).mp he

end Luce
