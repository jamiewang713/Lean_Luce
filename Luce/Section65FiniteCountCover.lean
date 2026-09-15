import Luce.Section65CoreCountComparison

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem filter_card_real65 {α : Type*} [Fintype α] (p : α → Prop) :
    ((Finset.univ.filter p).card : ℝ) = ∑ x : α, if p x then (1 : ℝ) else 0 := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem disjoint_indicators_sum_le_one65 {ι : Type*} [Fintype ι] (p : ι → Prop)
    (hd : ∀ i j, p i → p j → i = j) :
    (∑ i : ι, if p i then (1 : ℝ) else 0) ≤ 1 := by
  classical
  by_cases he : ∃ i, p i
  · obtain ⟨i,hi⟩ := he
    have hs : (∑ j : ι, if p j then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j hj hji
        have hjp : ¬ p j := fun h => hji (hd j i h hi)
        simp [hjp]
      · simp
    exact hs.le
  · have hp : ∀ i, ¬ p i := by simpa only [not_exists] using he
    simp [hp]

theorem disjoint_filter_card_sum_le65 {α ι : Type*} [Fintype α] [Fintype ι]
    (p : ι → α → Prop) (hd : ∀ x i j, p i x → p j x → i = j) :
    (∑ i : ι, ((Finset.univ.filter (p i)).card : ℝ)) ≤ (Fintype.card α : ℝ) := by
  simp_rw [filter_card_real65]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _ : α, (1 : ℝ) := Finset.sum_le_sum (fun x _ => disjoint_indicators_sum_le_one65 _ (hd x))
    _ = _ := by simp

theorem covered_filter_card65 {α ι : Type*} [Fintype α] [Fintype ι]
    (p : α → Prop) (q : ι → α → Prop) (h : ∀ x, p x ∨ ∃ i, q i x) :
    (Fintype.card α : ℝ) ≤ ((Finset.univ.filter p).card : ℝ)+
      ∑ i : ι, ((Finset.univ.filter (q i)).card : ℝ) := by
  classical
  simp_rw [filter_card_real65]
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  calc
    _ = ∑ _ : α, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      rcases h x with hp | ⟨i,hi⟩
      · simp only [hp,ite_true,le_add_iff_nonneg_right]
        exact Finset.sum_nonneg (fun j _ => by positivity)
      · have hsum := Finset.single_le_sum (s := Finset.univ)
          (f := fun j => if q j x then (1 : ℝ) else 0) (fun j _ => by positivity) (Finset.mem_univ i)
        simp only [hi,ite_true] at hsum
        exact hsum.trans (le_add_of_nonneg_left (by positivity))

end Luce.Section6
