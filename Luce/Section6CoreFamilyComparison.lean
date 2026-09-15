import Luce.Section6CoreFamilyIdealBounds
import Luce.Section6FiniteBadSetSum

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- The finite comparison retains arbitrary deterministic category
restrictions while using the local law only on separated assignments. -/
theorem core_family_comparison_of_bounds {s n A B r : ℕ}
    (side : Fin s → Corner) (behavior : Fin s → EndpointBehavior) (k : Fin s → ℕ)
    (P : ∀ c, (Fin (k c+1) → Fin n) → Prop) (w : Weights n)
    (M : Fin n → Fin n → ℝ) (hM : ∀ a b, 0 ≤ M a b)
    (hK : ∀ c (a b : Fin n), 0 ≤ localIdealKernel (side c) (behavior c)
      (cornerDistance (side c) a) (cornerDistance (side c) b))
    (E : CollisionAssignment n A B side k → ℝ) (hE : ∀ x, 0 ≤ E x)
    (bad : CollisionAssignment n A B side k → Prop)
    {C eps RM RI : ℝ} (hC : 0 ≤ C) (heps : 0 ≤ eps)
    (hcyl : ∀ t, t ≤ r → ∀ u j : Fin t → Fin n, Function.Injective u → Function.Injective j →
      (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} ≤ C*∏ a, M (u a) (j a))
    (hcard : Fintype.card (CollisionSlot k) ≤ r)
    (hinj : ∀ x, ¬ bad x → Function.Injective (collisionLabel x))
    (hlocal : ∀ x, ¬ bad x →
      |coreFamilyRankProbability w x - varyingCycleFamilyWeight side k
        (fun c a b => localIdealKernel (side c) (behavior c)
          (cornerDistance (side c) a) (cornerDistance (side c) b)) x| ≤ eps*E x)
    (hbadM : (∑ x : CollisionAssignment n A B side k,
      if bad x then varyingCycleFamilyWeight side k (fun _ => M) x else 0) ≤ RM)
    (hbadI : (∑ x : CollisionAssignment n A B side k,
      if bad x then varyingCycleFamilyWeight side k
        (fun c a b => localIdealKernel (side c) (behavior c)
          (cornerDistance (side c) a) (cornerDistance (side c) b)) x else 0) ≤ RI) :
    |(∑ x : CollisionAssignment n A B side k, coreFamilyActualWeight side k P w x) -
      (∑ x : CollisionAssignment n A B side k, coreFamilyIdealWeight side behavior k P x)| ≤
      eps*(∑ x, E x)+C*RM+RI := by
  let K : Fin s → Fin n → Fin n → ℝ := fun c a b =>
    localIdealKernel (side c) (behavior c) (cornerDistance (side c) a) (cornerDistance (side c) b)
  have hgood (x : CollisionAssignment n A B side k) (hx : ¬ bad x) :
      |coreFamilyActualWeight side k P w x-coreFamilyIdealWeight side behavior k P x| ≤ eps*E x := by
    have hi := hinj x hx
    rw [core_family_ideal_of_injective side behavior k P x hi]
    unfold coreFamilyActualWeight
    by_cases hP : ∀ c, P c (fun j => (x c j).val)
    · rw [if_pos ⟨hi, hP⟩, if_pos hP]
      exact hlocal x hx
    · rw [if_neg (fun h => hP h.2), if_neg hP, sub_self, abs_zero]
      exact mul_nonneg heps (hE x)
  have hh := finite_local_comparison
    (coreFamilyActualWeight side k P w) (coreFamilyIdealWeight side behavior k P) E
    (fun x => C*varyingCycleFamilyWeight side k (fun _ => M) x)
    (varyingCycleFamilyWeight side k K) bad heps
    (core_family_actual_nonneg side k P w) (core_family_ideal_nonneg side behavior k P hK) hE
    (core_family_actual_domination side k P w M hM hC hcyl hcard)
    (core_family_ideal_le_product side behavior k P hK) hgood
  have hscale : (∑ x : CollisionAssignment n A B side k,
      if bad x then C*varyingCycleFamilyWeight side k (fun _ => M) x else 0) =
      C*∑ x : CollisionAssignment n A B side k,
        if bad x then varyingCycleFamilyWeight side k (fun _ => M) x else 0 := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [hscale] at hh
  exact hh.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbadM hC)) hbadI)

end Luce.Section6
