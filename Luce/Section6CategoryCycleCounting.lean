import Luce.Section6CategoryCycleEquivalence

noncomputable section
open Function
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]

theorem category_collection_card (R : Equiv.Perm α) (k r : ι → ℕ) (P : ι → Finset α → Prop) :
    Nat.card (CategoryCycleCollection R k r P) =
      ∏ i, (categoryCycleSet R k P i).card.descFactorial (r i) := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [CategoryCycleCollection, Fintype.card_pi]

theorem category_roots_card {R : Equiv.Perm α} {k r : ι → ℕ} {P : ι → Finset α → Prop}
    (C : CategoryCycleCollection R k r P) :
    Nat.card (CategoryCycleRoots C) = ∏ i, (k i+1)^r i := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_pi]
  calc
    _ = ∏ _a : Fin (r i), (k i+1) := by
      apply Finset.prod_congr rfl
      intro a _
      rw [Fintype.card_coe]
      exact Section5.cycleOrbit_card R (k i) _ (Finset.mem_filter.mp (C i a).property).1
    _ = _ := by simp

theorem rooted_category_collection_card (R : Equiv.Perm α) (k r : ι → ℕ)
    (P : ι → Finset α → Prop) :
    Nat.card (RootedCategoryCollection R k r P) =
      (∏ i, (categoryCycleSet R k P i).card.descFactorial (r i)) * ∏ i, (k i+1)^r i := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hf (C : CategoryCycleCollection R k r P) :
      Fintype.card (CategoryCycleRoots C) = ∏ i, (k i+1)^r i := by
    rw [← Nat.card_eq_fintype_card]
    exact category_roots_card C
  simp_rw [hf]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, category_collection_card]

theorem category_assignment_card (R : Equiv.Perm α) (k r : ι → ℕ) (P : ι → Finset α → Prop)
    (hd : Pairwise (fun i j => Disjoint (categoryCycleSet R k P i) (categoryCycleSet R k P j))) :
    Nat.card (CategoryCycleAssignment R k r P) =
      (∏ i, (categoryCycleSet R k P i).card.descFactorial (r i)) * ∏ i, (k i+1)^r i := by
  rw [← Nat.card_congr (rootedCategoryEquivAssignment (r := r) hd)]
  exact rooted_category_collection_card R k r P

theorem category_root_factor_pos (k r : ι → ℕ) :
    0 < ∏ i, ((k i+1 : ℕ) : ℝ)^r i := by
  exact Finset.prod_pos (fun i _ => pow_pos (Nat.cast_pos.mpr (Nat.succ_pos (k i))) _)

theorem category_factorial_eq_assignment_card (R : Equiv.Perm α) (k r : ι → ℕ)
    (P : ι → Finset α → Prop)
    (hd : Pairwise (fun i j => Disjoint (categoryCycleSet R k P i) (categoryCycleSet R k P j))) :
    (∏ i, ((categoryCycleSet R k P i).card.descFactorial (r i) : ℝ)) =
      (Nat.card (CategoryCycleAssignment R k r P) : ℝ) / ∏ i, ((k i+1 : ℕ) : ℝ)^r i := by
  rw [category_assignment_card R k r P hd, Nat.cast_mul]
  simp only [Nat.cast_prod, Nat.cast_pow]
  exact (mul_div_cancel_right₀ _ (ne_of_gt (category_root_factor_pos k r))).symm

def categoryBlockIndicator (R : Equiv.Perm α) (k r : ι → ℕ)
    (t : CategoryCycleVertex k r ↪ α) : ℝ := by
  classical
  exact ∏ x, if R (t x) = t (categoryBlockPermutation k r x) then 1 else 0

theorem sum_category_block_indicator (R : Equiv.Perm α) (k r : ι → ℕ)
    (P : ι → Finset α → Prop) :
    (∑ t : CategoryCycleVertex k r ↪ α,
      if ∀ b, P b.1 (categoryBlockVertexSet t b) then categoryBlockIndicator R k r t else 0) =
      (Nat.card (CategoryCycleAssignment R k r P) : ℝ) := by
  classical
  have he (t : CategoryCycleVertex k r ↪ α) :
      (if ∀ b, P b.1 (categoryBlockVertexSet t b) then categoryBlockIndicator R k r t else 0) =
      if (∀ x, R (t x) = t (categoryBlockPermutation k r x)) ∧
        (∀ b, P b.1 (categoryBlockVertexSet t b)) then (1 : ℝ) else 0 := by
    by_cases hp : ∀ x, R (t x) = t (categoryBlockPermutation k r x)
    <;> by_cases hP : ∀ b, P b.1 (categoryBlockVertexSet t b)
    <;> simp [categoryBlockIndicator, Fintype.prod_boole, hp, hP]
  simp_rw [he]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Exact factorial expansion with category restrictions and all rotation
multiplicities, including empty categories and zero requested cycles. -/
theorem category_factorial_eq_assignment_sum (R : Equiv.Perm α) (k r : ι → ℕ)
    (P : ι → Finset α → Prop)
    (hd : Pairwise (fun i j => Disjoint (categoryCycleSet R k P i) (categoryCycleSet R k P j))) :
    (∏ i, ((categoryCycleSet R k P i).card.descFactorial (r i) : ℝ)) =
      (∑ t : CategoryCycleVertex k r ↪ α,
        if ∀ b, P b.1 (categoryBlockVertexSet t b) then categoryBlockIndicator R k r t else 0) /
        ∏ i, ((k i+1 : ℕ) : ℝ)^r i := by
  classical
  rw [sum_category_block_indicator]
  exact category_factorial_eq_assignment_card R k r P hd

end Luce.Section6
