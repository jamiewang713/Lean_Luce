import Luce.Section6CriticalBlocks
import Luce.Section6CriticalReferenceMass

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

def criticalReference (n A B k : ℕ) : ℝ :=
  if A ≤ k+1 ∧ k+1 ≤ B then
    1/(((k : ℝ)+1)*Real.log ((n : ℝ)/((k : ℝ)+1))) else 0

theorem critical_reference_row_sum (n A B : ℕ) (g : ℝ → ℝ) (hg : g 0 = 0) :
    (∑ k ∈ Finset.range n, g (criticalReference n A B k)) =
      ∑ k ∈ criticalBlock n A B,
        g (1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))) := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [criticalBlock,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  simp only [criticalReference]
  split_ifs <;> simp [hg]

theorem critical_reference_row_bounds {n A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (hBn : B ≤ n) (hzB : 1 ≤ Real.log (n : ℝ)-Real.log (B : ℝ)) (k : ℕ) :
    0 ≤ criticalReference n A B k ∧ criticalReference n A B k ≤ 1 := by
  classical
  by_cases hk : A ≤ k+1 ∧ k+1 ≤ B
  · have hkn : k < n := by omega
    have hz := hzB.trans (critical_block_log_lower hA
      (k := ⟨k,hkn⟩) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩))
    have hm : (1 : ℝ) ≤ (k : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    have hd : 1 ≤ ((k : ℝ)+1)*Real.log ((n : ℝ)/((k : ℝ)+1)) :=
      one_le_mul_of_one_le_of_one_le hm hz
    rw [criticalReference,if_pos hk]
    exact ⟨by positivity,(div_le_one (by linarith)).mpr hd⟩
  · simp only [criticalReference,if_neg hk]; norm_num

theorem critical_reference_row_mass {n A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (hBn : B ≤ n) :
    (∑ k ∈ Finset.range n, criticalReference n A B k) =
      ∑ m ∈ Finset.Icc A B, 1/((m : ℝ)*(Real.log (n : ℝ)-Real.log (m : ℝ))) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrow := critical_reference_row_sum n A B id rfl
  simp only [id_eq] at hrow
  rw [hrow]
  have he (k : Fin n) :
      1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1))) =
      1/(((k.val+1 : ℕ) : ℝ)*(Real.log (n : ℝ)-Real.log ((k.val+1 : ℕ) : ℝ))) := by
    push_cast
    rw [Real.log_div hn.ne' (by positivity)]
  simp only [id_eq,he]
  exact critical_block_sum hA hBn (fun m => 1/((m : ℝ)*(Real.log (n : ℝ)-Real.log (m : ℝ))))

theorem critical_reference_error_split {n A B : ℕ} (hAB : A ≤ B)
    (p : Fin n → ℝ) (hp : ∀ k, 0 ≤ p k) :
    (∑ k, |p k-criticalReference n A B k.val|) ≤
      (∑ k ∈ criticalBlock n 1 A, p k)+
      (∑ k ∈ criticalBlock n A B,
        |p k-1/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))|)+
      ∑ k ∈ criticalBlock n (B+1) n, p k := by
  classical
  simp only [criticalBlock,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  by_cases hl : k.val+1 < A
  · have h1 : 1 ≤ k.val+1 ∧ k.val+1 ≤ A := by omega
    have h2 : ¬(A ≤ k.val+1 ∧ k.val+1 ≤ B) := by omega
    have h3 : ¬(B+1 ≤ k.val+1 ∧ k.val+1 ≤ n) := by omega
    simp only [criticalReference,if_pos h1,if_neg h2,if_neg h3,sub_zero,add_zero,abs_of_nonneg (hp k),le_refl]
  · by_cases hu : k.val+1 ≤ B
    · have h2 : A ≤ k.val+1 ∧ k.val+1 ≤ B := by omega
      have h3 : ¬(B+1 ≤ k.val+1 ∧ k.val+1 ≤ n) := by omega
      simp only [criticalReference,if_pos h2,if_neg h3,add_zero]
      split_ifs <;> linarith [hp k]
    · have h1 : ¬(1 ≤ k.val+1 ∧ k.val+1 ≤ A) := by omega
      have h2 : ¬(A ≤ k.val+1 ∧ k.val+1 ≤ B) := by omega
      have h3 : B+1 ≤ k.val+1 ∧ k.val+1 ≤ n := ⟨by omega,k.isLt⟩
      simp only [criticalReference,if_neg h1,if_neg h2,if_pos h3,sub_zero,zero_add,abs_of_nonneg (hp k),le_refl]

end Luce.Section6
