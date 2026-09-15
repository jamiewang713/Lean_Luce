import Luce.Section6CategoryCycleDefinitions

noncomputable section
open Function
open scoped BigOperators
namespace Luce.Section6

variable {α ι : Type*} [Fintype α] [DecidableEq α]

def categoryAssignmentBlock {R : Equiv.Perm α} {k r : ι → ℕ} {P : ι → Finset α → Prop}
    (t : CategoryCycleAssignment R k r P) (b : CategoryCycleSlot r) : Section5.RootedCycle R (k b.1) := by
  let e : Fin (k b.1+1) ↪ α := ⟨fun a => t.1 ⟨b, a⟩, fun a c h => by
    apply Fin.ext
    exact congrArg (fun x : CategoryCycleVertex k r => x.2.val) (t.1.injective h)⟩
  exact ⟨e, (Section5.isRootedCycle_iff_rotate R (k b.1) e).mpr (fun a => t.2.1 ⟨b, a⟩)⟩

theorem category_assignment_orbit_set {R : Equiv.Perm α} {k r : ι → ℕ}
    {P : ι → Finset α → Prop} (t : CategoryCycleAssignment R k r P) (b : CategoryCycleSlot r) :
    (periodicOrbit (R : α → α) (t.1 ⟨b, 0⟩)).toFinset = categoryBlockVertexSet t.1 b := by
  ext y
  rw [Section5.mem_periodicOrbit_toFinset]
  change (y ∈ periodicOrbit (R : α → α) ((categoryAssignmentBlock t b).1 0)) ↔ _
  rw [Section5.rootedCycle_mem_periodicOrbit_iff]
  simp [categoryBlockVertexSet, categoryAssignmentBlock]
  rfl

def categoryCollectionBlock {R : Equiv.Perm α} {k r : ι → ℕ} {P : ι → Finset α → Prop}
    (C : RootedCategoryCollection R k r P) (b : CategoryCycleSlot r) : Section5.RootedCycle R (k b.1) := by
  classical
  exact Section5.rootedCycleOfPeriodicPoint R (k b.1) ⟨(C.2 b.1 b.2).val,
    Section5.minimalPeriod_of_mem_cycleOrbit R (k b.1) _
      (Finset.mem_filter.mp (C.1 b.1 b.2).property).1 _ (C.2 b.1 b.2).property⟩

theorem category_collection_block_mem {R : Equiv.Perm α} {k r : ι → ℕ}
    {P : ι → Finset α → Prop} (C : RootedCategoryCollection R k r P)
    (b : CategoryCycleSlot r) (a : Fin (k b.1+1)) :
    (categoryCollectionBlock C b).1 a ∈ (C.1 b.1 b.2).val.toFinset := by
  classical
  have he := Section5.periodicOrbit_eq_of_mem_cycleOrbit R (k b.1) _
    (Finset.mem_filter.mp (C.1 b.1 b.2).property).1 _ (C.2 b.1 b.2).property
  rw [← he, Section5.mem_periodicOrbit_toFinset]
  exact (Section5.rootedCycle_mem_periodicOrbit_iff (categoryCollectionBlock C b) _).mpr ⟨a, rfl⟩

theorem category_collection_distinct {R : Equiv.Perm α} {k r : ι → ℕ}
    {P : ι → Finset α → Prop}
    (hd : Pairwise (fun i j => Disjoint (categoryCycleSet R k P i) (categoryCycleSet R k P j)))
    (C : CategoryCycleCollection R k r P) (b c : CategoryCycleSlot r) (hbc : b ≠ c) :
    (C b.1 b.2).val ≠ (C c.1 c.2).val := by
  classical
  rcases b with ⟨i, a⟩
  rcases c with ⟨j, b⟩
  intro he
  by_cases hij : i = j
  · subst j
    have hab := (C i).injective (Subtype.ext he)
    exact hbc (congrArg (fun a => (⟨i, a⟩ : CategoryCycleSlot r)) hab)
  · apply Finset.disjoint_left.mp (hd hij) (C i a).property
    rw [he]
    exact (C j b).property

theorem category_collection_disjoint {R : Equiv.Perm α} {k r : ι → ℕ}
    {P : ι → Finset α → Prop}
    (hd : Pairwise (fun i j => Disjoint (categoryCycleSet R k P i) (categoryCycleSet R k P j)))
    (C : CategoryCycleCollection R k r P) (b c : CategoryCycleSlot r) (hbc : b ≠ c) :
    Disjoint (C b.1 b.2).val.toFinset (C c.1 c.2).val.toFinset := by
  classical
  exact Section5.cycleOrbits_disjoint R (k b.1) (k c.1) _ _
    (Finset.mem_filter.mp (C b.1 b.2).property).1
    (Finset.mem_filter.mp (C c.1 c.2).property).1
    (category_collection_distinct hd C b c hbc)

end Luce.Section6
