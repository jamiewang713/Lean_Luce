import Luce.Section6CoreFamilyDefinitions
import Luce.Section6CategoryCycleDefinitions

noncomputable section
open scoped BigOperators
namespace Luce.Section6

def categoryCoreVertexEquiv {q s : ℕ} (c : Fin q → CoreCycleCategory) (r : Fin q → ℕ)
    (e : Fin s ≃ CategoryCycleSlot r) :
    CollisionSlot (fun a => (c (e a).1).lengthIndex) ≃
      CategoryCycleVertex (fun i => (c i).lengthIndex) r :=
  Equiv.sigmaCongrLeft (β := fun b : CategoryCycleSlot r => Fin ((c b.1).lengthIndex+1)) e

def categoryCoreFamilyEquiv {q s n A B : ℕ} (c : Fin q → CoreCycleCategory) (r : Fin q → ℕ)
    (e : Fin s ≃ CategoryCycleSlot r) :
    CollisionAssignment n A B (fun a => (c (e a).1).side) (fun a => (c (e a).1).lengthIndex) ≃
      (∀ v : CategoryCycleVertex (fun i => (c i).lengthIndex) r,
        CollisionCore n A B (c v.1.1).side) :=
  (Equiv.piCongrLeft (fun b : CategoryCycleSlot r =>
    Fin ((c b.1).lengthIndex+1) → CollisionCore n A B (c b.1).side) e).trans
    (Equiv.piCurry (fun (b : CategoryCycleSlot r) (_j : Fin ((c b.1).lengthIndex+1)) =>
      CollisionCore n A B (c b.1).side)).symm

theorem category_core_family_equiv_apply {q s n A B : ℕ}
    (c : Fin q → CoreCycleCategory) (r : Fin q → ℕ) (e : Fin s ≃ CategoryCycleSlot r)
    (x : CollisionAssignment n A B (fun a => (c (e a).1).side) (fun a => (c (e a).1).lengthIndex))
    (a : Fin s) (j : Fin ((c (e a).1).lengthIndex+1)) :
    categoryCoreFamilyEquiv c r e x ⟨e a, j⟩ = x a j := by
  change ((Equiv.piCongrLeft (fun b : CategoryCycleSlot r =>
    Fin ((c b.1).lengthIndex+1) → CollisionCore n A B (c b.1).side) e) x) (e a) j = x a j
  rw [Equiv.piCongrLeft_apply_apply]

theorem category_core_vertex_equiv_rotate {q s : ℕ}
    (c : Fin q → CoreCycleCategory) (r : Fin q → ℕ) (e : Fin s ≃ CategoryCycleSlot r)
    (p : CollisionSlot (fun a => (c (e a).1).lengthIndex)) :
    categoryBlockPermutation (fun i => (c i).lengthIndex) r (categoryCoreVertexEquiv c r e p) =
      categoryCoreVertexEquiv c r e (collisionBlockPermutation (fun a => (c (e a).1).lengthIndex) p) := rfl

theorem category_core_enumeration_injective {q s n A B : ℕ}
    (c : Fin q → CoreCycleCategory) (r : Fin q → ℕ) (e : Fin s ≃ CategoryCycleSlot r)
    (x : CollisionAssignment n A B (fun a => (c (e a).1).side) (fun a => (c (e a).1).lengthIndex)) :
    Function.Injective (fun v => (categoryCoreFamilyEquiv c r e x v).val) ↔
      Function.Injective (collisionLabel x) := by
  have he (p : CollisionSlot (fun a => (c (e a).1).lengthIndex)) :
      (categoryCoreFamilyEquiv c r e x (categoryCoreVertexEquiv c r e p)).val = collisionLabel x p := by
    obtain ⟨a, j⟩ := p
    exact congrArg Subtype.val (category_core_family_equiv_apply c r e x a j)
  constructor
  · intro hx p q hpq
    apply (categoryCoreVertexEquiv c r e).injective
    apply hx
    simpa only [he] using hpq
  · intro hx p q hpq
    obtain ⟨p, rfl⟩ := (categoryCoreVertexEquiv c r e).surjective p
    obtain ⟨q, rfl⟩ := (categoryCoreVertexEquiv c r e).surjective q
    exact congrArg (categoryCoreVertexEquiv c r e) (hx (by simpa only [he] using hpq))

theorem category_core_enumeration_restrictions {q s n A B : ℕ}
    (c : Fin q → CoreCycleCategory) (r : Fin q → ℕ) (e : Fin s ≃ CategoryCycleSlot r)
    (x : CollisionAssignment n A B (fun a => (c (e a).1).side) (fun a => (c (e a).1).lengthIndex)) :
    (∀ b : CategoryCycleSlot r, CategoryAdmissible A B (c b.1)
      (categoryBlockVertexSet (fun v => (categoryCoreFamilyEquiv c r e x v).val) b)) ↔
    ∀ a : Fin s, (c (e a).1).rootWindow.Allows n
      (categorySetRootDepth (c (e a).1).side (Finset.univ.image (fun j => (x a j).val))) := by
  classical
  have hs (a : Fin s) :
      categoryBlockVertexSet (fun v => (categoryCoreFamilyEquiv c r e x v).val) (e a) =
        Finset.univ.image (fun j => (x a j).val) := by
    simp only [categoryBlockVertexSet, category_core_family_equiv_apply]
  constructor
  · intro hx a
    have hh := (hx (e a)).2
    rwa [hs a] at hh
  · intro hx b
    obtain ⟨a, rfl⟩ := e.surjective b
    unfold CategoryAdmissible
    rw [hs a]
    refine ⟨?_, hx a⟩
    intro v hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact (x a j).property

theorem category_core_enumeration_rank_event {q s n A B : ℕ}
    (c : Fin q → CoreCycleCategory) (r : Fin q → ℕ) (e : Fin s ≃ CategoryCycleSlot r)
    (x : CollisionAssignment n A B (fun a => (c (e a).1).side) (fun a => (c (e a).1).lengthIndex)) :
    {clocks | ∀ v : CategoryCycleVertex (fun i => (c i).lengthIndex) r,
      raceRank clocks (categoryCoreFamilyEquiv c r e x v).val =
        (categoryCoreFamilyEquiv c r e x (categoryBlockPermutation (fun i => (c i).lengthIndex) r v)).val.val+1} =
    {clocks | ∀ p : CollisionSlot (fun a => (c (e a).1).lengthIndex), raceRank clocks (collisionLabel x p) =
      (collisionLabel x (collisionBlockPermutation (fun a => (c (e a).1).lengthIndex) p)).val+1} := by
  have he (p : CollisionSlot (fun a => (c (e a).1).lengthIndex)) :
      (categoryCoreFamilyEquiv c r e x (categoryCoreVertexEquiv c r e p)).val = collisionLabel x p := by
    obtain ⟨a, j⟩ := p
    exact congrArg Subtype.val (category_core_family_equiv_apply c r e x a j)
  ext clocks
  constructor
  · intro h p
    simpa only [category_core_vertex_equiv_rotate, he] using h (categoryCoreVertexEquiv c r e p)
  · intro h v
    obtain ⟨p, rfl⟩ := (categoryCoreVertexEquiv c r e).surjective v
    simpa only [category_core_vertex_equiv_rotate, he] using h p

end Luce.Section6
