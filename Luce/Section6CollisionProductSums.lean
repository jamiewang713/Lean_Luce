import Luce.Section6CollisionPaths
import Mathlib.Logic.Equiv.Prod

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem collision_prod_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : ι → ℝ) : (∏ c, f c) = f i*∏ c : {c // c ≠ i}, f c.val := by
  rw [Fintype.prod_eq_mul_prod_compl i]
  rw [Finset.prod_subtype (p := fun c => c ≠ i) _ (by simp)]

theorem collision_card_complement {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Fintype.card {c : ι // c ≠ i} = Fintype.card ι-1 := by
  simpa using Fintype.card_subtype_compl (fun c : ι => c = i)

theorem collision_product_test_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (w : ∀ i, β i → ℝ)
    (i : ι) (g : β i → ℝ) :
    (∑ x : ∀ i, β i, (∏ c, w c (x c))*g (x i)) =
      (∑ a, w i a*g a)*(∏ c : {c // c ≠ i}, ∑ a, w c.val a) := by
  rw [← Fintype.sum_equiv (Equiv.piSplitAt i β).symm
    (fun ay : β i × (∀ c : {c // c ≠ i}, β c.val) =>
      (w i ay.1*(∏ c, w c.val (ay.2 c)))*g ay.1) _ (by
      intro ay
      rw [collision_prod_split i]
      have he (c : {c // c ≠ i}) : ((Equiv.piSplitAt i β).symm ay) c.val = ay.2 c := by
        simp [Equiv.piSplitAt, c.property]
      simp_rw [he]
      simp [Equiv.piSplitAt])]
  simp only [Fintype.sum_prod_type]
  rw [Fintype.prod_sum]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro y _; ring

theorem collision_product_test_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (w : ∀ i, β i → ℝ)
    (i j : ι) (hji : j ≠ i) (g : β i → β j → ℝ) :
    (∑ x : ∀ i, β i, (∏ c, w c (x c))*g (x i) (x j)) =
      (∑ a, ∑ b, w i a*w j b*g a b)*
        (∏ c : {c : {c // c ≠ i} // c ≠ ⟨j, hji⟩}, ∑ a, w c.val.val a) := by
  rw [← Fintype.sum_equiv (Equiv.piSplitAt i β).symm
    (fun ay : β i × (∀ c : {c // c ≠ i}, β c.val) =>
      (w i ay.1*(∏ c, w c.val (ay.2 c)))*g ay.1 (ay.2 ⟨j, hji⟩)) _ (by
      intro ay
      rw [collision_prod_split i]
      have he (c : {c // c ≠ i}) : ((Equiv.piSplitAt i β).symm ay) c.val = ay.2 c := by
        simp [Equiv.piSplitAt, c.property]
      simp_rw [he]
      simp [Equiv.piSplitAt, hji])]
  simp only [Fintype.sum_prod_type]
  have he (a : β i) :
      (∑ y : ∀ c : {c // c ≠ i}, β c.val,
        (w i a*(∏ c, w c.val (y c)))*g a (y ⟨j, hji⟩)) =
      w i a*((∑ b, w j b*g a b)*
        (∏ c : {c : {c // c ≠ i} // c ≠ ⟨j, hji⟩}, ∑ b, w c.val.val b)) := by
    rw [← collision_product_test_one (fun c : {c // c ≠ i} => w c.val) ⟨j, hji⟩ (g a)]
    simp only [Finset.mul_sum, mul_assoc]
  simp_rw [he]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _; ring

theorem collision_complement_product_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (t : ι → ℝ) (ht : ∀ c, 0 ≤ t c) {T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ c, t c ≤ T) :
    (∏ c : {c // c ≠ i}, t c.val) ≤ T^(Fintype.card ι-1) := by
  calc
    _ ≤ ∏ _c : {c // c ≠ i}, T := Finset.prod_le_prod (fun c _ => ht c.val) (fun c _ => hb c.val)
    _ = _ := by simp [collision_card_complement]

theorem collision_two_complement_product_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hji : j ≠ i) (t : ι → ℝ) (ht : ∀ c, 0 ≤ t c) {T : ℝ} (hT : 1 ≤ T)
    (hb : ∀ c, t c ≤ T) :
    (∏ c : {c : {c // c ≠ i} // c ≠ ⟨j, hji⟩}, t c.val.val) ≤ T^(Fintype.card ι-1) := by
  have hcard : Fintype.card {c : {c // c ≠ i} // c ≠ ⟨j, hji⟩} ≤ Fintype.card ι-1 := by
    rw [← collision_card_complement i]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  calc
    _ ≤ ∏ _c : {c : {c // c ≠ i} // c ≠ ⟨j, hji⟩}, T :=
      Finset.prod_le_prod (fun c _ => ht c.val.val) (fun c _ => hb c.val.val)
    _ = T^(Fintype.card {c : {c // c ≠ i} // c ≠ ⟨j, hji⟩}) := by simp
    _ ≤ _ := pow_le_pow_right₀ hT hcard

end Luce.Section6
