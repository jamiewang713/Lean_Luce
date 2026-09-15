import Luce.Section5CycleAssignments

/-! Finite category counting with arbitrary deterministic restrictions on
the vertex set of a cycle. These definitions do not assume a probability
law or a local approximation. -/
noncomputable section
open scoped BigOperators
namespace Luce.Section6

abbrev CategoryCycleSlot {ι : Type*} (r : ι → ℕ) := Σ i, Fin (r i)
abbrev CategoryCycleVertex {ι : Type*} (k r : ι → ℕ) := Σ b : CategoryCycleSlot r, Fin (k b.1+1)

def categoryBlockPermutation {ι : Type*} (k r : ι → ℕ) : Equiv.Perm (CategoryCycleVertex k r) :=
  Equiv.sigmaCongrRight (fun b => finRotate (k b.1+1))

def categoryCycleSet {α ι : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α) (k : ι → ℕ) (P : ι → Finset α → Prop) (i : ι) : Finset (Cycle α) := by
  classical
  exact (Section5.cycleOrbits R (k i)).filter (fun c => P i c.toFinset)

abbrev CategoryCycleCollection {α ι : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α) (k r : ι → ℕ) (P : ι → Finset α → Prop) :=
  ∀ i, Fin (r i) ↪ ↥(categoryCycleSet R k P i)

abbrev CategoryCycleRoots {α ι : Type*} [Fintype α] [DecidableEq α]
    {R : Equiv.Perm α} {k r : ι → ℕ} {P : ι → Finset α → Prop}
    (C : CategoryCycleCollection R k r P) := ∀ i a, ↥((C i a).val.toFinset)

abbrev RootedCategoryCollection {α ι : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α) (k r : ι → ℕ) (P : ι → Finset α → Prop) :=
  Σ C : CategoryCycleCollection R k r P, CategoryCycleRoots C

def categoryBlockVertexSet {α ι : Type*} [DecidableEq α] {k r : ι → ℕ}
    (t : CategoryCycleVertex k r → α) (b : CategoryCycleSlot r) : Finset α :=
  Finset.univ.image (fun a : Fin (k b.1+1) => t ⟨b, a⟩)

abbrev CategoryCycleAssignment {α ι : Type*} [DecidableEq α]
    (R : Equiv.Perm α) (k r : ι → ℕ) (P : ι → Finset α → Prop) :=
  {t : CategoryCycleVertex k r ↪ α //
    (∀ x, R (t x) = t (categoryBlockPermutation k r x)) ∧
    ∀ b : CategoryCycleSlot r, P b.1 (categoryBlockVertexSet t b)}

end Luce.Section6
