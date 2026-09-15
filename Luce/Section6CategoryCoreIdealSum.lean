import Luce.Section6CategoryCoreActualSum
import Luce.Section6CoreIdealCategorySum

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem category_slot_product {q s : ℕ} (r : Fin q → ℕ)
    (e : Fin s ≃ CategoryCycleSlot r) (f : Fin q → ℝ) :
    (∏ a : Fin s, f (e a).1) = ∏ i, (f i)^r i := by
  calc
    _ = ∏ b : CategoryCycleSlot r, f b.1 := Equiv.prod_comp e _
    _ = _ := by rw [Fintype.prod_sigma]; simp

theorem category_rotation_factor_ge_one {q : ℕ} (c : Fin q → CoreCycleCategory)
    (r : Fin q → ℕ) : 1 ≤ ∏ i, (((c i).lengthIndex+1 : ℕ) : ℝ)^r i := by
  apply Finset.one_le_prod
  intro i _
  apply one_le_pow₀
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le (c i).lengthIndex)

theorem core_category_ideal_product_eq_family_sum {q s n : ℕ}
    (hA : 1 ≤ idealCoreLower n) (hB : idealCoreUpper n ≤ n)
    (left right : EndpointBehavior) (c : Fin q → CoreCycleCategory)
    (r : Fin q → ℕ) (e : Fin s ≃ CategoryCycleSlot r) :
    (∏ i, coreCategoryIdealMean left right n (c i)^r i) =
      (∑ x : CollisionAssignment n (idealCoreLower n) (idealCoreUpper n)
          (fun a => (c (e a).1).side) (fun a => (c (e a).1).lengthIndex),
        coreFamilyIdealWeight (fun a => (c (e a).1).side)
          (fun a => cornerBehavior left right (c (e a).1).side)
          (fun a => (c (e a).1).lengthIndex) (categoryFamilyRestriction c r e) x) /
        ∏ i, (((c i).lengthIndex+1 : ℕ) : ℝ)^r i := by
  classical
  rw [core_family_ideal_sum_factors]
  have hterm (a : Fin s) :
      (∑ x : Fin ((c (e a).1).lengthIndex+1) →
          CollisionCore n (idealCoreLower n) (idealCoreUpper n) (c (e a).1).side,
        if Function.Injective (fun j => (x j).val) ∧
          categoryFamilyRestriction c r e a (fun j => (x j).val) then
          idealCycleWeight (c (e a).1).side (cornerBehavior left right (c (e a).1).side)
            (c (e a).1).lengthIndex (fun j => cornerDistance (c (e a).1).side (x j).val) else 0) =
        coreCategoryIdealMean left right n (c (e a).1)*(((c (e a).1).lengthIndex+1 : ℕ) : ℝ) := by
    have hh := core_category_mean_eq_tuple_sum hA hB left right (c (e a).1)
    have hd : ((c (e a).1).lengthIndex : ℝ)+1 ≠ 0 := by positivity
    have hh' := (eq_div_iff hd).mp hh
    simpa only [Nat.cast_add, Nat.cast_one, categoryFamilyRestriction,
      idealCycleWeight, collisionCycleWeight] using hh'.symm
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib,
    category_slot_product r e (fun i => coreCategoryIdealMean left right n (c i)),
    category_slot_product r e (fun i => (((c i).lengthIndex+1 : ℕ) : ℝ))]
  exact (mul_div_cancel_right₀ _ (ne_of_gt (zero_lt_one.trans_le
    (category_rotation_factor_ge_one c r)))).symm

end Luce.Section6
