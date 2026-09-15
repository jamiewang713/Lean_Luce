import Luce.Section6CategoryCycleBlocks

noncomputable section
open Function
open scoped BigOperators
namespace Luce.Section6

variable {α ι : Type*} [Fintype α] [DecidableEq α]

def categoryAssignmentOfCollection {R : Equiv.Perm α} {k r : ι → ℕ}
    {P : ι → Finset α → Prop}
    (hd : Pairwise (fun i j => Disjoint (categoryCycleSet R k P i) (categoryCycleSet R k P j)))
    (C : RootedCategoryCollection R k r P) : CategoryCycleAssignment R k r P := by
  classical
  let e : CategoryCycleVertex k r ↪ α :=
    ⟨fun x => (categoryCollectionBlock C x.1).1 x.2, ?_⟩
  · refine ⟨e, ⟨?_, ?_⟩⟩
    · intro x
      exact (Section5.isRootedCycle_iff_rotate R (k x.1.1) (categoryCollectionBlock C x.1).1).mp
        (categoryCollectionBlock C x.1).2 x.2
    · intro b
      have hs : categoryBlockVertexSet e b = (C.1 b.1 b.2).val.toFinset := by
        ext y
        have he := Section5.periodicOrbit_eq_of_mem_cycleOrbit R (k b.1) _
          (Finset.mem_filter.mp (C.1 b.1 b.2).property).1 _ (C.2 b.1 b.2).property
        rw [← he, Section5.mem_periodicOrbit_toFinset]
        change _ ↔ y ∈ periodicOrbit (R : α → α) ((categoryCollectionBlock C b).1 0)
        rw [Section5.rootedCycle_mem_periodicOrbit_iff]
        simp [categoryBlockVertexSet, e]
        rfl
      rw [hs]
      exact (Finset.mem_filter.mp (C.1 b.1 b.2).property).2
  · intro x y he
    obtain ⟨b, a⟩ := x
    obtain ⟨c, d⟩ := y
    dsimp only at he
    by_cases hbc : b = c
    · subst c
      have had := (categoryCollectionBlock C b).1.injective he
      exact congrArg (fun a => (⟨b, a⟩ : CategoryCycleVertex k r)) had
    · exact (Finset.disjoint_left.mp (category_collection_disjoint hd C.1 b c hbc)
        (category_collection_block_mem C b a) (he.symm ▸ category_collection_block_mem C c d)).elim

def categoryCollectionOfAssignment {R : Equiv.Perm α} {k r : ι → ℕ}
    {P : ι → Finset α → Prop}
    (t : CategoryCycleAssignment R k r P) : RootedCategoryCollection R k r P := by
  classical
  let C : CategoryCycleCollection R k r P := fun i =>
    ⟨fun a => ⟨periodicOrbit (R : α → α) (t.1 ⟨⟨i, a⟩, 0⟩), by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_image.mpr
          refine ⟨t.1 ⟨⟨i, a⟩, 0⟩, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Section5.rootedCycle_minimalPeriod (categoryAssignmentBlock t ⟨i, a⟩)⟩
        · rw [category_assignment_orbit_set]
          exact t.2.2 ⟨i, a⟩⟩,
      ?_⟩
  · refine ⟨C, fun i a => ⟨t.1 ⟨⟨i, a⟩, 0⟩, ?_⟩⟩
    change t.1 ⟨⟨i, a⟩, 0⟩ ∈
      (periodicOrbit (R : α → α) (t.1 ⟨⟨i, a⟩, 0⟩)).toFinset
    rw [Section5.mem_periodicOrbit_toFinset]
    exact (Section5.rootedCycle_mem_periodicOrbit_iff (categoryAssignmentBlock t ⟨i, a⟩) _).mpr ⟨0, rfl⟩
  · intro a b hab
    have he := congrArg Subtype.val hab
    dsimp only at he
    have hb : t.1 ⟨⟨i, b⟩, 0⟩ ∈
        periodicOrbit (R : α → α) (t.1 ⟨⟨i, a⟩, 0⟩) := by
      rw [he]
      exact (Section5.rootedCycle_mem_periodicOrbit_iff (categoryAssignmentBlock t ⟨i, b⟩) _).mpr ⟨0, rfl⟩
    obtain ⟨s, hs⟩ := (Section5.rootedCycle_mem_periodicOrbit_iff
      (categoryAssignmentBlock t ⟨i, a⟩) _).mp hb
    apply Fin.ext
    exact congrArg (fun x : CategoryCycleVertex k r => x.1.2.val) (t.1.injective hs)

theorem categoryAssignmentOfCollection_collectionOfAssignment {R : Equiv.Perm α}
    {k r : ι → ℕ} {P : ι → Finset α → Prop}
    (hd : Pairwise (fun i j => Disjoint (categoryCycleSet R k P i) (categoryCycleSet R k P j)))
    (t : CategoryCycleAssignment R k r P) :
    categoryAssignmentOfCollection hd (categoryCollectionOfAssignment t) = t := by
  apply Subtype.ext
  apply Function.Embedding.ext
  intro x
  change (R : α → α)^[x.2.val] (t.1 ⟨x.1, 0⟩) = t.1 x
  exact (Section5.rootedCycle_eq_iterate (categoryAssignmentBlock t x.1) x.2).symm

theorem categoryCollectionOfAssignment_assignmentOfCollection {R : Equiv.Perm α}
    {k r : ι → ℕ} {P : ι → Finset α → Prop}
    (hd : Pairwise (fun i j => Disjoint (categoryCycleSet R k P i) (categoryCycleSet R k P j)))
    (C : RootedCategoryCollection R k r P) :
    categoryCollectionOfAssignment (categoryAssignmentOfCollection hd C) = C := by
  classical
  have hc : (categoryCollectionOfAssignment (categoryAssignmentOfCollection hd C)).1 = C.1 := by
    funext i
    apply Function.Embedding.ext
    intro a
    apply Subtype.ext
    change periodicOrbit (R : α → α) (C.2 i a).val = (C.1 i a).val
    exact Section5.periodicOrbit_eq_of_mem_cycleOrbit R (k i) _
      (Finset.mem_filter.mp (C.1 i a).property).1 _ (C.2 i a).property
  apply Sigma.ext hc
  apply Function.hfunext rfl
  intro i i' hi
  have hi' := eq_of_heq hi
  subst i'
  apply Function.hfunext rfl
  intro a b hab
  have hab' := eq_of_heq hab
  subst b
  apply (Subtype.heq_iff_coe_eq (fun x => ?_)).mpr
  · rfl
  · rw [hc]

/-- Rooted, ordered category collections are exactly compatible global
injections satisfying the deterministic category restrictions. -/
def rootedCategoryEquivAssignment {R : Equiv.Perm α} {k r : ι → ℕ}
    {P : ι → Finset α → Prop}
    (hd : Pairwise (fun i j => Disjoint (categoryCycleSet R k P i) (categoryCycleSet R k P j))) :
    RootedCategoryCollection R k r P ≃ CategoryCycleAssignment R k r P where
  toFun := categoryAssignmentOfCollection hd
  invFun := categoryCollectionOfAssignment
  left_inv := categoryCollectionOfAssignment_assignmentOfCollection hd
  right_inv := categoryAssignmentOfCollection_collectionOfAssignment hd

end Luce.Section6
