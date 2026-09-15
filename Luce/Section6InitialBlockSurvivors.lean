import Luce.Section6Sampling

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Removing at most k-h labels leaves at least h labels in the first k.
All their positive rates contribute to the actual remaining total rate. -/
theorem initial_block_remaining_rate {n k h : ℕ} (w : Weights n)
    (hkn : k ≤ n) (removed : Finset (Fin n)) (hcard : removed.card+h ≤ k)
    {a : ℝ} (ha : 0 ≤ a) (hrate : ∀ i : Fin n, i.val+1 ≤ k → a ≤ w.rate i) :
    (h : ℝ)*a ≤ ∑ i ∈ Finset.univ \ removed, w.rate i := by
  classical
  let e : Fin k ↪ Fin n :=
    ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩,
      fun i j hij => Fin.ext (congrArg (fun z : Fin n => z.val) hij)⟩
  let block := Finset.univ.map e
  have hbcard : block.card = k := by simp [block]
  have hkeep : h ≤ (block \ removed).card := by
    have hh := Finset.le_card_sdiff removed block
    rw [hbcard] at hh
    omega
  have hbound : ∀ i ∈ block \ removed, a ≤ w.rate i := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_sdiff.mp hi).1
    exact hrate _ (Nat.succ_le_of_lt j.isLt)
  calc
    _ ≤ ((block \ removed).card : ℝ)*a :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hkeep) ha
    _ = ∑ _i ∈ block \ removed, a := by simp
    _ ≤ ∑ i ∈ block \ removed, w.rate i := Finset.sum_le_sum hbound
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro i hi; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩)
      (fun i _ _ => (w.positive i).le)

end Luce.Section6
