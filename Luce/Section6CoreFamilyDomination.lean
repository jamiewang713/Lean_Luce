import Luce.Section6CoreFamilyDefinitions
import Luce.Section6FiniteRankReindex

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem core_family_actual_nonneg {s n A B : ℕ} (side : Fin s → Corner) (k : Fin s → ℕ)
    (P : ∀ c, (Fin (k c+1) → Fin n) → Prop) (w : Weights n)
    (x : CollisionAssignment n A B side k) : 0 ≤ coreFamilyActualWeight side k P w x := by
  unfold coreFamilyActualWeight
  split_ifs
  · exact measureReal_nonneg
  · exact le_rfl

theorem core_family_actual_domination {s n A B r : ℕ} (side : Fin s → Corner) (k : Fin s → ℕ)
    (P : ∀ c, (Fin (k c+1) → Fin n) → Prop) (w : Weights n)
    (M : Fin n → Fin n → ℝ) (hM : ∀ a b, 0 ≤ M a b) {C : ℝ} (hC : 0 ≤ C)
    (hcyl : ∀ t, t ≤ r → ∀ u j : Fin t → Fin n, Function.Injective u → Function.Injective j →
      (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} ≤ C*∏ a, M (u a) (j a))
    (hcard : Fintype.card (CollisionSlot k) ≤ r) (x : CollisionAssignment n A B side k) :
    coreFamilyActualWeight side k P w x ≤ C*varyingCycleFamilyWeight side k (fun _ => M) x := by
  unfold coreFamilyActualWeight
  split_ifs with hx
  · have hh := finite_rank_cylinder_domination w M C hcyl hcard (collisionLabel x)
      (fun p => collisionLabel x (collisionBlockPermutation k p)) hx.1
      (hx.1.comp (collisionBlockPermutation k).injective)
    rw [Fintype.prod_sigma] at hh
    exact hh
  · exact mul_nonneg hC (varying_cycle_family_nonneg side k (fun _ => M) (fun _ => hM) x)

theorem core_family_injective_of_separated {s n A B : ℕ} {side : Fin s → Corner} {k : Fin s → ℕ}
    (D : ℕ) (x : CollisionAssignment n A B side k)
    (hsep : ¬ ∃ p q : CollisionSlot k, p ≠ q ∧ collisionNearby D p q x) :
    Function.Injective (collisionLabel x) := by
  intro p q he
  by_contra hpq
  apply hsep ⟨p, q, hpq, ?_⟩
  unfold collisionNearby
  rw [he, Nat.dist_self]
  exact Nat.zero_le _

theorem core_family_block_injective {s n A B : ℕ} {side : Fin s → Corner} {k : Fin s → ℕ}
    (x : CollisionAssignment n A B side k) (hx : Function.Injective (collisionLabel x)) (c : Fin s) :
    Function.Injective (fun j => (x c j).val) := by
  intro i j hij
  have he : (⟨c, i⟩ : CollisionSlot k) = ⟨c, j⟩ := hx hij
  apply Fin.ext
  exact congrArg (fun p : CollisionSlot k => p.2.val) he

end Luce.Section6
