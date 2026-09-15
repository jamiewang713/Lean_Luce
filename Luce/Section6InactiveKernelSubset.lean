import Luce.Section6InactiveKernelRow

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem inactive_terminal_kernel_subset_bound {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (theta : ℝ), 0 < n → 0 < theta →
    ∀ s : Finset (Fin n), (∀ j ∈ s, 16384*terminalDepth j ≤ n) →
    (∑ j ∈ s, ((theta/(terminalDepth j : ℝ))*
      ((terminalDepth j : ℝ)/(n : ℝ))^(d*theta)+
        Real.exp (-d*Real.sqrt ((n : ℝ)*(terminalDepth j : ℝ))))) ≤ C := by
  obtain ⟨C, hC, hb⟩ := inactive_terminal_kernel_row_bound hd
  refine ⟨C, hC, ?_⟩
  intro n theta hn ht s hs
  classical
  let g : ℕ → ℝ := fun k => (theta/((k : ℝ)+1))*(((k : ℝ)+1)/(n : ℝ))^(d*theta)+
    Real.exp (-d*Real.sqrt ((n : ℝ)*((k : ℝ)+1)))
  let T := s.image (fun j => j.rev.val)
  have hdepth (j : Fin n) : j.rev.val+1 = terminalDepth j := by
    rw [Fin.val_rev]
    unfold terminalDepth
    omega
  have he : (∑ j ∈ s, ((theta/(terminalDepth j : ℝ))*
      ((terminalDepth j : ℝ)/(n : ℝ))^(d*theta)+
        Real.exp (-d*Real.sqrt ((n : ℝ)*(terminalDepth j : ℝ))))) = ∑ k ∈ T, g k := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j _
      have hj : (j.rev.val : ℝ)+1 = (terminalDepth j : ℝ) := by exact_mod_cast hdepth j
      simp only [g, hj]
    · intro a ha b hb hab
      exact Fin.rev_injective (Fin.ext hab)
  have hsub : T ⊆ Finset.range (n/16384) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hh := hs j hj
    have he := hdepth j
    apply Finset.mem_range.mpr
    omega
  have hdom : (∑ k ∈ T, g k) ≤ ∑ k ∈ Finset.range (n/16384), g k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by dsimp [g]; positivity)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hhalf : 2*((n/16384 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (show 2*(n/16384) ≤ n by omega)
  rw [he]
  exact hdom.trans (hb (n : ℝ) theta hn1 ht (n/16384) hhalf)

end Luce.Section6
