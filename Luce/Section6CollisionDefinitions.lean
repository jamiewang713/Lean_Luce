import Luce.Section6ContractDefinitions
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Nat.Dist

/-! Literal finite sums in Lemma 6.9. Cycles are ordered lists of vertex
slots; repetitions are allowed, as required for bounding their removal. -/
noncomputable section
open scoped BigOperators
namespace Luce.Section6

abbrev CollisionCore (n A B : ℕ) (side : Corner) :=
  {v : Fin n // A ≤ cornerDistance side v ∧ cornerDistance side v ≤ B}

def collisionCycleWeight {α : Type*} (F : α → α → ℝ) (k : ℕ)
    (x : Fin (k+1) → α) : ℝ :=
  ∏ j, F (x j) (x (finRotate (k+1) j))

abbrev CollisionSlot {s : ℕ} (k : Fin s → ℕ) := Σ c, Fin (k c+1)

abbrev CollisionAssignment {s : ℕ} (n A B : ℕ) (side : Fin s → Corner)
    (k : Fin s → ℕ) := ∀ c, Fin (k c+1) → CollisionCore n A B (side c)

def collisionLabel {s n A B : ℕ} {side : Fin s → Corner} {k : Fin s → ℕ}
    (x : CollisionAssignment n A B side k) (p : CollisionSlot k) : Fin n :=
  (x p.1 p.2).val

def collisionFamilyWeight {s n A B : ℕ} (side : Fin s → Corner) (k : Fin s → ℕ)
    (F : Fin n → Fin n → ℝ) (x : CollisionAssignment n A B side k) : ℝ :=
  ∏ c, collisionCycleWeight (fun a b => F a.val b.val) (k c) (x c)

def collisionNearby {s n A B : ℕ} {side : Fin s → Corner} {k : Fin s → ℕ}
    (D : ℕ) (p q : CollisionSlot k) (x : CollisionAssignment n A B side k) : Prop :=
  Nat.dist (collisionLabel x p).val (collisionLabel x q).val ≤ D

def collisionPairSum {s n A B : ℕ} {side : Fin s → Corner} {k : Fin s → ℕ}
    (W : CollisionAssignment n A B side k → ℝ) (D : ℕ) (p q : CollisionSlot k) : ℝ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (collisionNearby D p q), W x

def collisionUnionSum {s n A B : ℕ} {side : Fin s → Corner} {k : Fin s → ℕ}
    (W : CollisionAssignment n A B side k → ℝ) (D : ℕ) : ℝ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (fun x =>
    ∃ p q : CollisionSlot k, p ≠ q ∧ collisionNearby D p q x), W x

end Luce.Section6
