import Luce.Section5CycleAssignments

/-!
# The factorial expansion with an arbitrary vertex cutoff

Source: `fixed_points.tex:1281–1295`. The short cycles counted there have all
vertices in the bulk set. The restriction below is imposed on actual cycles
and on every label of the compatible injection. No invariance of the cutoff
set under the permutation is assumed.
-/

noncomputable section
open Function
open scoped BigOperators

namespace Luce.Section5

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every vertex of every selected cycle belongs to the cutoff. -/
def CycleCollectionWithin {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (S : Finset α) (C : CycleCollection R L m) : Prop :=
  ∀ ell a, (C ell a).val.toFinset ⊆ S

abbrev RootedCycleCollectionWithin (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :=
  {C : RootedCycleCollection R L m // CycleCollectionWithin S C.1}

abbrev CycleAssignmentWithin (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :=
  {t : CycleAssignment R L m // ∀ x, t.1 x ∈ S}

/-- The root enumeration covers the whole cycle, so imposing the cutoff on
labels is equivalent to imposing it on all vertices of each selected cycle. -/
theorem collectionWithin_iff_assignmentWithin {R : Equiv.Perm α}
    {L : ℕ} {m : Fin L → ℕ} (S : Finset α) (C : RootedCycleCollection R L m) :
    CycleCollectionWithin S C.1 ↔ ∀ x, (assignmentOfCollection C).1 x ∈ S := by
  constructor
  · intro h x
    exact h x.1.1 x.1.2 (collectionBlock_mem C x.1 x.2)
  · intro h ell a y hy
    have he := periodicOrbit_eq_of_mem_cycleOrbit R ell.val _
      (C.1 ell a).property _ (C.2 ell a).property
    have hym : y ∈ periodicOrbit (R : α → α) ((collectionBlock C ⟨ell, a⟩).1 0) := by
      change y ∈ periodicOrbit (R : α → α) (C.2 ell a).val
      apply (mem_periodicOrbit_toFinset R _ y).mp
      rw [he]
      exact hy
    obtain ⟨b, hb⟩ := (rootedCycle_mem_periodicOrbit_iff (collectionBlock C ⟨ell, a⟩) y).mp hym
    exact hb ▸ h ⟨⟨ell, a⟩, b⟩

/-- The full labelled-cycle bijection restricts to any cutoff set, including
the empty set, even when the cutoff is not invariant under R. -/
def rootedCollectionWithinEquivAssignmentWithin (R : Equiv.Perm α)
    (L : ℕ) (m : Fin L → ℕ) (S : Finset α) :
    RootedCycleCollectionWithin R L m S ≃ CycleAssignmentWithin R L m S :=
  (rootedCollectionEquivAssignment R L m).subtypeEquiv
    (collectionWithin_iff_assignmentWithin S)

/-- Actual permutation cycles of length k+1 all of whose vertices lie in S. -/
def cycleOrbitsWithin (R : Equiv.Perm α) (S : Finset α) (k : ℕ) : Finset (Cycle α) := by
  classical
  exact (cycleOrbits R k).filter (fun c => c.toFinset ⊆ S)

def cycleCountWithin (R : Equiv.Perm α) (S : Finset α) (k : ℕ) : ℕ :=
  (cycleOrbitsWithin R S k).card

theorem cycleCountWithin_univ (R : Equiv.Perm α) (k : ℕ) :
    cycleCountWithin R Finset.univ k = cycleCount R k := by
  simp [cycleCountWithin, cycleOrbitsWithin, cycleCount]

/-- Ordered distinct cycles selected directly from the cutoff cycle set. -/
abbrev CutoffCycleCollection (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :=
  (ell : Fin L) → (Fin (m ell) ↪ ↥(cycleOrbitsWithin R S ell.val))

/-- Restricting the ambient collection and selecting from the filtered cycle
set are exactly equivalent, without strengthening the cutoff condition. -/
def collectionWithinEquivCutoffCollection (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    {C : CycleCollection R L m // CycleCollectionWithin S C} ≃
      CutoffCycleCollection R L m S where
  toFun C ell :=
    ⟨fun a => ⟨(C.1 ell a).val, Finset.mem_filter.mpr ⟨(C.1 ell a).property, C.2 ell a⟩⟩,
      fun a b h => (C.1 ell).injective
        (Subtype.ext (congrArg (fun c : ↥(cycleOrbitsWithin R S ell.val) => c.val) h))⟩
  invFun C :=
    ⟨fun ell => ⟨fun a => ⟨(C ell a).val, (Finset.mem_filter.mp (C ell a).property).1⟩,
      fun a b h => (C ell).injective
        (Subtype.ext (congrArg (fun c : ↥(cycleOrbits R ell.val) => c.val) h))⟩,
      fun ell a => (Finset.mem_filter.mp (C ell a).property).2⟩
  left_inv C := by
    apply Subtype.ext
    funext ell
    apply Function.Embedding.ext
    intro a
    rfl
  right_inv C := by
    funext ell
    apply Function.Embedding.ext
    intro a
    rfl

theorem cutoffCycleCollection_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    Nat.card (CutoffCycleCollection R L m S) =
      ∏ ell : Fin L, (cycleCountWithin R S ell.val).descFactorial (m ell) := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [CutoffCycleCollection, Fintype.card_pi, cycleCountWithin]

theorem collectionWithin_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    Nat.card {C : CycleCollection R L m // CycleCollectionWithin S C} =
      ∏ ell : Fin L, (cycleCountWithin R S ell.val).descFactorial (m ell) := by
  rw [Nat.card_congr (collectionWithinEquivCutoffCollection R L m S)]
  exact cutoffCycleCollection_card R L m S

/-- Restricting a cycle collection does not alter its number of roots: every
selected cycle retains all of its length-many vertices. -/
theorem rootedCycleCollectionWithin_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    Nat.card (RootedCycleCollectionWithin R L m S) =
      (∏ ell : Fin L, (cycleCountWithin R S ell.val).descFactorial (m ell)) *
        ∏ ell : Fin L, (ell.val + 1) ^ m ell := by
  classical
  rw [Nat.card_congr (Equiv.subtypeSigmaEquiv
    (fun C : CycleCollection R L m => CycleRoots C) (CycleCollectionWithin S))]
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hf (C : {C : CycleCollection R L m // CycleCollectionWithin S C}) :
      Fintype.card (CycleRoots C.1) = ∏ ell : Fin L, (ell.val + 1) ^ m ell := by
    rw [← Nat.card_eq_fintype_card]
    exact cycleRoots_card C.1
  simp_rw [hf]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, collectionWithin_card]

/-- The cutoff-compatible global injection has exactly the requested falling
factorial count times the original rotational multiplicity. -/
theorem cycleAssignmentWithin_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    Nat.card (CycleAssignmentWithin R L m S) =
      (∏ ell : Fin L, (cycleCountWithin R S ell.val).descFactorial (m ell)) *
        ∏ ell : Fin L, (ell.val + 1) ^ m ell := by
  rw [← Nat.card_congr (rootedCollectionWithinEquivAssignmentWithin R L m S)]
  exact rootedCycleCollectionWithin_card R L m S

theorem cutoff_cycle_factorial_eq_assignment_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    (∏ ell : Fin L, ((cycleCountWithin R S ell.val).descFactorial (m ell) : ℝ)) =
      (Nat.card (CycleAssignmentWithin R L m S) : ℝ) /
        ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell := by
  rw [cycleAssignmentWithin_card, Nat.cast_mul]
  simp only [Nat.cast_prod, Nat.cast_pow]
  exact (mul_div_cancel_right₀ _ (ne_of_gt (cycleAssignment_rootFactor_pos L m))).symm

/-- The cutoff restriction is imposed on every labelled vertex, as in the
paper's sum over distinct bulk indices. -/
def cycleBlockIndicatorWithin (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ)
    (S : Finset α) (t : CycleVertex L m ↪ α) : ℝ := by
  classical
  exact if ∀ x, t x ∈ S then cycleBlockIndicator R L m t else 0

theorem sum_cycleBlockIndicatorWithin (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    (∑ t : CycleVertex L m ↪ α, cycleBlockIndicatorWithin R L m S t) =
      (Nat.card (CycleAssignmentWithin R L m S) : ℝ) := by
  classical
  have he : CycleAssignmentWithin R L m S ≃
      {t : CycleVertex L m ↪ α //
        (∀ x, R (t x) = t (cycleBlockPermutation L m x)) ∧ (∀ x, t x ∈ S)} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun t : CycleVertex L m ↪ α => ∀ x, R (t x) = t (cycleBlockPermutation L m x))
      (fun t : CycleVertex L m ↪ α => ∀ x, t x ∈ S)
  have hw (t : CycleVertex L m ↪ α) :
      cycleBlockIndicatorWithin R L m S t =
        if (∀ x, R (t x) = t (cycleBlockPermutation L m x)) ∧ (∀ x, t x ∈ S)
        then 1 else 0 := by
    by_cases hp : ∀ x, R (t x) = t (cycleBlockPermutation L m x)
    <;> by_cases hs : ∀ x, t x ∈ S
    <;> simp [cycleBlockIndicatorWithin, cycleBlockIndicator, Fintype.prod_boole, hp, hs]
  simp_rw [hw]
  rw [Finset.sum_boole, Nat.card_congr he, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- The exact deterministic factorial expansion at source 1281–1284 for
cycles wholly inside an arbitrary cutoff. All labels are distinct, edge
orientations are the prescribed block rotations, and every rotation factor
is retained. Empty cutoffs and zero multiplicities require no exceptions. -/
theorem cutoff_cycle_factorial_eq_assignment_sum (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) (S : Finset α) :
    (∏ ell : Fin L, ((cycleCountWithin R S ell.val).descFactorial (m ell) : ℝ)) =
      (∑ t : CycleVertex L m ↪ α, cycleBlockIndicatorWithin R L m S t) /
        ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell := by
  rw [sum_cycleBlockIndicatorWithin]
  exact cutoff_cycle_factorial_eq_assignment_card R L m S

/-- The paper's bulk labels are one-based; `Fin n` stores label i as i-1. -/
def bulkCycleLabelSet (n : ℕ) (a : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i.val : ℝ) + 1 ≤ a * n)

def bulkCycleCount {n : ℕ} (R : Equiv.Perm (Fin n)) (a : ℝ) (k : ℕ) : ℕ :=
  cycleCountWithin R (bulkCycleLabelSet n a) k

/-- Literal source instantiation: the cycle count C^(a) counts only cycles
whose one-based labels are at most a*n. The displayed summation condition
imposes that same bound on every vertex of the global injection. -/
theorem bulk_cycle_factorial_eq_assignment_sum {n : ℕ}
    (R : Equiv.Perm (Fin n)) (L : ℕ) (m : Fin L → ℕ) (a : ℝ) :
    (∏ ell : Fin L, ((bulkCycleCount R a ell.val).descFactorial (m ell) : ℝ)) =
      (∑ t : CycleVertex L m ↪ Fin n,
        if ∀ x, ((t x).val : ℝ) + 1 ≤ a * n then cycleBlockIndicator R L m t else 0) /
        ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell := by
  classical
  simpa only [bulkCycleCount, cycleBlockIndicatorWithin, bulkCycleLabelSet,
    Finset.mem_filter, Finset.mem_univ, true_and] using
    cutoff_cycle_factorial_eq_assignment_sum R L m (bulkCycleLabelSet n a)

end Luce.Section5
