import Luce.Section6CollisionProductSums

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem finite_or_weight_sum {α : Type*} [Fintype α]
    (W : α → ℝ) (hW : ∀ x, 0 ≤ W x) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    (∑ x, if P x ∨ Q x then W x else 0) ≤
      (∑ x, if P x then W x else 0)+(∑ x, if Q x then W x else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq, hW x]

theorem finite_union_weight_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (W : α → ℝ) (hW : ∀ x, 0 ≤ W x) (P : ι → α → Prop) :
    (∑ x, if ∃ i, P i x then W x else 0) ≤ ∑ i, ∑ x, if P i x then W x else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : ∃ i, P i x
  · obtain ⟨i, hi⟩ := hp
    rw [if_pos ⟨i, hi⟩]
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if P j x then W x else 0)
      (fun j _ => by split_ifs <;> first | exact hW x | exact le_rfl) (Finset.mem_univ i)
    simpa only [if_pos hi] using hh
  · rw [if_neg hp]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hW x | exact le_rfl)

/-- Finite comparison with a common bad set. No relation between that set
and a random gap variable, including independence, is required. -/
theorem finite_local_comparison {α : Type*} [Fintype α]
    (P I E U V : α → ℝ) (bad : α → Prop) {eps : ℝ} (heps : 0 ≤ eps)
    (hP : ∀ x, 0 ≤ P x) (hI : ∀ x, 0 ≤ I x) (hE : ∀ x, 0 ≤ E x)
    (hU : ∀ x, P x ≤ U x) (hV : ∀ x, I x ≤ V x)
    (hgood : ∀ x, ¬ bad x → |P x-I x| ≤ eps*E x) :
    |(∑ x, P x)-(∑ x, I x)| ≤ eps*(∑ x, E x) +
      (∑ x, if bad x then U x else 0) + (∑ x, if bad x then V x else 0) := by
  have hp (x : α) : |P x-I x| ≤ eps*E x +
      (if bad x then U x else 0) + (if bad x then V x else 0) := by
    by_cases hb : bad x
    · rw [if_pos hb, if_pos hb]
      have hh : |P x-I x| ≤ P x+I x := abs_sub_le_iff.mpr ⟨by linarith [hI x], by linarith [hP x]⟩
      have hz := mul_nonneg heps (hE x)
      linarith [hU x, hV x]
    · rw [if_neg hb, if_neg hb, add_zero, add_zero]
      exact hgood x hb
  calc
    _ = |∑ x, (P x-I x)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ x, |P x-I x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, (eps*E x+(if bad x then U x else 0)+(if bad x then V x else 0)) :=
      Finset.sum_le_sum (fun x _ => hp x)
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

end Luce.Section6
