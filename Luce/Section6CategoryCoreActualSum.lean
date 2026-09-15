import Luce.Section6CategoryCoreEnumeration
import Luce.Section6CoreCategoryDisjoint
import Luce.Section6RestrictedAssignmentSums

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

def categoryFamilyRestriction {q s n : ℕ} (c : Fin q → CoreCycleCategory)
    (r : Fin q → ℕ) (e : Fin s ≃ CategoryCycleSlot r)
    (a : Fin s) (t : Fin ((c (e a).1).lengthIndex+1) → Fin n) : Prop :=
  (c (e a).1).rootWindow.Allows n
    (categorySetRootDepth (c (e a).1).side (Finset.univ.image t))

theorem category_core_actual_sum_reindex {q s n A B : ℕ}
    (c : Fin q → CoreCycleCategory) (r : Fin q → ℕ) (e : Fin s ≃ CategoryCycleSlot r)
    (w : Weights n) :
    (∑ t : CategoryCycleVertex (fun i => (c i).lengthIndex) r ↪ Fin n,
      if ∀ b, CategoryAdmissible A B (c b.1) (categoryBlockVertexSet t b) then
        (exponentialRace w).real {z | ∀ v, raceRank z (t v) =
          (t (categoryBlockPermutation (fun i => (c i).lengthIndex) r v)).val+1} else 0) =
    ∑ x : CollisionAssignment n A B (fun a => (c (e a).1).side) (fun a => (c (e a).1).lengthIndex),
      coreFamilyActualWeight (fun a => (c (e a).1).side) (fun a => (c (e a).1).lengthIndex)
        (categoryFamilyRestriction c r e) w x := by
  classical
  let V := CategoryCycleVertex (fun i => (c i).lengthIndex) r
  let Q (v : V) (a : Fin n) := A ≤ cornerDistance (c v.1.1).side a ∧
    cornerDistance (c v.1.1).side a ≤ B
  let P (t : V → Fin n) := ∀ b, CategoryAdmissible A B (c b.1) (categoryBlockVertexSet t b)
  let f (t : V → Fin n) := (exponentialRace w).real {z | ∀ v, raceRank z (t v) =
    (t (categoryBlockPermutation (fun i => (c i).lengthIndex) r v)).val+1}
  have hP (t : V → Fin n) (ht : P t) (v : V) : Q v (t v) :=
    (ht v.1).1 (t v) (Finset.mem_image.mpr ⟨v.2, Finset.mem_univ _, rfl⟩)
  have hh := restricted_embedding_sum Q P hP f
  calc
    _ = ∑ t : V ↪ Fin n, if P t then f t else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : P t
      · exact (if_pos ht).trans (if_pos ht).symm
      · exact (if_neg ht).trans (if_neg ht).symm
    _ = ∑ x : ∀ v : V, {a // Q v a},
        if Function.Injective (fun v => (x v).val) ∧ P (fun v => (x v).val) then
          f (fun v => (x v).val) else 0 := hh
    _ = _ := by
      symm
      apply Fintype.sum_equiv (categoryCoreFamilyEquiv c r e)
      intro x
      have hc := and_congr (category_core_enumeration_injective c r e x)
        (category_core_enumeration_restrictions c r e x)
      change (if _ then coreFamilyRankProbability w x else 0) = _
      by_cases hx : Function.Injective (collisionLabel x) ∧
          ∀ a, categoryFamilyRestriction c r e a (fun j => (x a j).val)
      · rw [if_pos hx, if_pos (hc.mpr hx)]
        exact congrArg (fun S => (exponentialRace w).real S)
          (category_core_enumeration_rank_event c r e x).symm
      · rw [if_neg hx, if_neg (fun h => hx (hc.mp h))]

theorem core_category_expectation_eq_family_sum {q s n : ℕ}
    (hn : 2 ≤ n) (hB : 2*idealCoreUpper n < n+1)
    (c : Fin q → CoreCycleCategory) (hc : CoreCategoriesDisjoint c)
    (r : Fin q → ℕ) (e : Fin s ≃ CategoryCycleSlot r) (w : Weights n) :
    (∫ z, ∏ i, ((coreCategoryCount (raceRankPermutation z) (c i)).descFactorial (r i) : ℝ)
      ∂exponentialRace w) =
      (∑ x : CollisionAssignment n (idealCoreLower n) (idealCoreUpper n)
          (fun a => (c (e a).1).side) (fun a => (c (e a).1).lengthIndex),
        coreFamilyActualWeight (fun a => (c (e a).1).side) (fun a => (c (e a).1).lengthIndex)
          (categoryFamilyRestriction c r e) w x) /
        ∏ i, (((c i).lengthIndex+1 : ℕ) : ℝ)^r i := by
  rw [core_category_expectation_eq_rank_sum hn hB w c hc r,
    category_core_actual_sum_reindex c r e w]

end Luce.Section6
