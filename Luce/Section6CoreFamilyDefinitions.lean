import Luce.Section6FactorialFamilyBounds
import Luce.Section6CoreCategoryDefinitions

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

def collisionBlockPermutation {s : ℕ} (k : Fin s → ℕ) : Equiv.Perm (CollisionSlot k) :=
  Equiv.sigmaCongrRight (fun c => finRotate (k c+1))

def coreFamilyRankProbability {s n A B : ℕ} {side : Fin s → Corner} {k : Fin s → ℕ}
    (w : Weights n) (x : CollisionAssignment n A B side k) : ℝ :=
  (exponentialRace w).real {e | ∀ p : CollisionSlot k, raceRank e (collisionLabel x p) =
    (collisionLabel x (collisionBlockPermutation k p)).val+1}

def coreFamilyActualWeight {s n A B : ℕ} (side : Fin s → Corner) (k : Fin s → ℕ)
    (P : ∀ c, (Fin (k c+1) → Fin n) → Prop) (w : Weights n)
    (x : CollisionAssignment n A B side k) : ℝ :=
  if Function.Injective (collisionLabel x) ∧ (∀ c, P c (fun j => (x c j).val)) then
    coreFamilyRankProbability w x else 0

def coreFamilyIdealWeight {s n A B : ℕ} (side : Fin s → Corner)
    (behavior : Fin s → EndpointBehavior) (k : Fin s → ℕ)
    (P : ∀ c, (Fin (k c+1) → Fin n) → Prop)
    (x : CollisionAssignment n A B side k) : ℝ :=
  ∏ c, if Function.Injective (fun j => (x c j).val) ∧ P c (fun j => (x c j).val) then
    idealCycleWeight (side c) (behavior c) (k c) (fun j => cornerDistance (side c) (x c j).val) else 0

theorem core_family_ideal_sum_factors {s n A B : ℕ} (side : Fin s → Corner)
    (behavior : Fin s → EndpointBehavior) (k : Fin s → ℕ)
    (P : ∀ c, (Fin (k c+1) → Fin n) → Prop) :
    (∑ x : CollisionAssignment n A B side k, coreFamilyIdealWeight side behavior k P x) =
      ∏ c, ∑ x : Fin (k c+1) → CollisionCore n A B (side c),
        if Function.Injective (fun j => (x j).val) ∧ P c (fun j => (x j).val) then
          idealCycleWeight (side c) (behavior c) (k c) (fun j => cornerDistance (side c) (x j).val) else 0 :=
    by
  exact (Fintype.prod_sum (fun c (x : Fin (k c+1) → CollisionCore n A B (side c)) =>
    if Function.Injective (fun j => (x j).val) ∧ P c (fun j => (x j).val) then
      idealCycleWeight (side c) (behavior c) (k c) (fun j => cornerDistance (side c) (x j).val) else 0)).symm

end Luce.Section6
