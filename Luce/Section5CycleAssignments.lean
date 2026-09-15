import Luce.Section5Cycles
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The labelled assignment expansion for joint cycle factorials

Source: `fixed_points.tex:1279–1295`. The vertex type is the explicit disjoint
union of the requested cycles. Its permutation rotates each block once. The
equivalence below retains every root and every ordered cycle slot.
-/

noncomputable section
open Function
open scoped BigOperators

namespace Luce.Section5

variable {α : Type*}

/-- Ordered cycle slots; `ell.val+1` is the actual cycle length. -/
abbrev CycleSlot (L : ℕ) (m : Fin L → ℕ) := Σ ell : Fin L, Fin (m ell)

/-- The disjoint labelled vertex set used in the factorial expansion. -/
abbrev CycleVertex (L : ℕ) (m : Fin L → ℕ) :=
  Σ b : CycleSlot L m, Fin (b.1.val + 1)

/-- The prescribed permutation sends each vertex to the next vertex of its
own directed cycle, including wraparound and singleton blocks. -/
def cycleBlockPermutation (L : ℕ) (m : Fin L → ℕ) : Equiv.Perm (CycleVertex L m) :=
  Equiv.sigmaCongrRight (fun b => finRotate (b.1.val + 1))

/-- All labelled vertices are distinct, and all prescribed edges occur in R. -/
abbrev CycleAssignment (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :=
  {t : CycleVertex L m ↪ α // ∀ x, R (t x) = t (cycleBlockPermutation L m x)}

lemma isRootedCycle_iff_rotate (R : Equiv.Perm α) (k : ℕ) (t : Fin (k + 1) ↪ α) :
    IsRootedCycle R k t ↔ ∀ a, R (t a) = t (finRotate (k + 1) a) := by
  have hrot (a : Fin k) : finRotate (k + 1) a.castSucc = a.succ := finRotate_of_lt a.isLt
  constructor
  · intro h a
    refine Fin.lastCases ?_ (fun b => ?_) a
    · simpa only [finRotate_last] using h.2
    · simpa only [hrot] using h.1 b
  · intro h
    refine ⟨fun a => ?_, ?_⟩
    · simpa only [hrot] using h a.castSucc
    · simpa only [finRotate_last] using h (Fin.last k)

/-- Restrict a global assignment to one of its blocks. -/
def assignmentBlock {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (t : CycleAssignment R L m) (b : CycleSlot L m) : RootedCycle R b.1.val := by
  let e : Fin (b.1.val + 1) ↪ α :=
    ⟨fun a => t.1 ⟨b, a⟩, fun a c h => by
      apply Fin.ext
      exact congrArg (fun x : CycleVertex L m => x.2.val) (t.1.injective h)⟩
  refine ⟨e, (isRootedCycle_iff_rotate R b.1.val e).mpr ?_⟩
  intro a
  exact t.2 ⟨b, a⟩

lemma rootedCycle_mem_periodicOrbit_iff {R : Equiv.Perm α} {k : ℕ}
    (t : RootedCycle R k) (y : α) :
    y ∈ periodicOrbit (R : α → α) (t.1 0) ↔ ∃ a : Fin (k + 1), t.1 a = y := by
  simp only [periodicOrbit, Cycle.mem_coe_iff, List.mem_map, List.mem_range,
    rootedCycle_minimalPeriod t]
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨⟨a, ha⟩, (rootedCycle_eq_iterate t ⟨a, ha⟩).trans he⟩
  · rintro ⟨a, he⟩
    exact ⟨a.val, a.isLt, (rootedCycle_eq_iterate t a).symm.trans he⟩

section Finite
variable [Fintype α] [DecidableEq α]

/-- Every vertex of an actual cycle recovers precisely that rotation class. -/
theorem periodicOrbit_eq_of_mem_cycleOrbit (R : Equiv.Perm α) (k : ℕ)
    (c : Cycle α) (hc : c ∈ cycleOrbits R k) (x : α) (hx : x ∈ c.toFinset) :
    periodicOrbit (R : α → α) x = c := by
  classical
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
  have hyp : y ∈ periodicPts (R : α → α) :=
    minimalPeriod_pos_iff_mem_periodicPts.mp (by
      have hh := (Finset.mem_filter.mp hy).2
      omega)
  obtain ⟨a, rfl⟩ := (mem_periodicOrbit_iff hyp).mp
    ((mem_periodicOrbit_toFinset R y x).mp hx)
  exact periodicOrbit_apply_iterate_eq hyp a

theorem minimalPeriod_of_mem_cycleOrbit (R : Equiv.Perm α) (k : ℕ)
    (c : Cycle α) (hc : c ∈ cycleOrbits R k) (x : α) (hx : x ∈ c.toFinset) :
    minimalPeriod (R : α → α) x = k + 1 := by
  have he := congrArg Cycle.length (periodicOrbit_eq_of_mem_cycleOrbit R k c hc x hx)
  simpa only [periodicOrbit_length, cycleOrbit_length R k c hc] using he

/-- Enumerate the selected cycle starting at its selected root. -/
def collectionBlock {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : RootedCycleCollection R L m) (b : CycleSlot L m) : RootedCycle R b.1.val :=
  rootedCycleOfPeriodicPoint R b.1.val ⟨(C.2 b.1 b.2).val,
    minimalPeriod_of_mem_cycleOrbit R b.1.val _ (C.1 b.1 b.2).property _
      (C.2 b.1 b.2).property⟩

lemma collectionBlock_mem {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : RootedCycleCollection R L m) (b : CycleSlot L m) (a : Fin (b.1.val + 1)) :
    (collectionBlock C b).1 a ∈ (C.1 b.1 b.2).val.toFinset := by
  have he := periodicOrbit_eq_of_mem_cycleOrbit R b.1.val _
    (C.1 b.1 b.2).property _ (C.2 b.1 b.2).property
  rw [← he, mem_periodicOrbit_toFinset]
  exact (rootedCycle_mem_periodicOrbit_iff (collectionBlock C b) _).mpr ⟨a, rfl⟩

/-- Assemble all blocks into one injection. Distinct cycle slots are
vertex-disjoint by the proved permutation-cycle disjointness theorem. -/
def assignmentOfCollection {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : RootedCycleCollection R L m) : CycleAssignment R L m := by
  let e : CycleVertex L m ↪ α :=
    ⟨fun x => (collectionBlock C x.1).1 x.2, ?_⟩
  · refine ⟨e, ?_⟩
    intro x
    exact (isRootedCycle_iff_rotate R x.1.1.val (collectionBlock C x.1).1).mp
      (collectionBlock C x.1).2 x.2
  · intro x y he
    obtain ⟨b, a⟩ := x
    obtain ⟨c, d⟩ := y
    dsimp only at he
    by_cases hbc : b = c
    · subst c
      have had := (collectionBlock C b).1.injective he
      exact congrArg (fun a => (⟨b, a⟩ : CycleVertex L m)) had
    · have hd := C.1.disjoint b.1 c.1 b.2 c.2 hbc
      exact (Finset.disjoint_left.mp hd (collectionBlock_mem C b a)
        (he.symm ▸ collectionBlock_mem C c d)).elim

/-- A global compatible injection recovers the ordered cycle classes and
their roots. Global injectivity excludes duplicate classes within a length. -/
def collectionOfAssignment {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (t : CycleAssignment R L m) : RootedCycleCollection R L m := by
  let C : CycleCollection R L m := fun ell =>
    ⟨fun a => ⟨periodicOrbit (R : α → α) (t.1 ⟨⟨ell, a⟩, 0⟩), by
        apply Finset.mem_image.mpr
        refine ⟨t.1 ⟨⟨ell, a⟩, 0⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          rootedCycle_minimalPeriod (assignmentBlock t ⟨ell, a⟩)⟩⟩,
      ?_⟩
  · refine ⟨C, fun ell a => ⟨t.1 ⟨⟨ell, a⟩, 0⟩, ?_⟩⟩
    change t.1 ⟨⟨ell, a⟩, 0⟩ ∈
      (periodicOrbit (R : α → α) (t.1 ⟨⟨ell, a⟩, 0⟩)).toFinset
    rw [mem_periodicOrbit_toFinset]
    exact (rootedCycle_mem_periodicOrbit_iff (assignmentBlock t ⟨ell, a⟩) _).mpr ⟨0, rfl⟩
  · intro a b hab
    have he := congrArg Subtype.val hab
    dsimp only at he
    have hb : t.1 ⟨⟨ell, b⟩, 0⟩ ∈
        periodicOrbit (R : α → α) (t.1 ⟨⟨ell, a⟩, 0⟩) := by
      rw [he]
      exact (rootedCycle_mem_periodicOrbit_iff (assignmentBlock t ⟨ell, b⟩) _).mpr ⟨0, rfl⟩
    obtain ⟨s, hs⟩ := (rootedCycle_mem_periodicOrbit_iff (assignmentBlock t ⟨ell, a⟩) _).mp hb
    apply Fin.ext
    exact congrArg (fun x : CycleVertex L m => x.1.2.val) (t.1.injective hs)

theorem assignmentOfCollection_collectionOfAssignment {R : Equiv.Perm α}
    {L : ℕ} {m : Fin L → ℕ} (t : CycleAssignment R L m) :
    assignmentOfCollection (collectionOfAssignment t) = t := by
  apply Subtype.ext
  apply Function.Embedding.ext
  intro x
  change (R : α → α)^[x.2.val] (t.1 ⟨x.1, 0⟩) = t.1 x
  exact (rootedCycle_eq_iterate (assignmentBlock t x.1) x.2).symm

theorem collectionOfAssignment_assignmentOfCollection {R : Equiv.Perm α}
    {L : ℕ} {m : Fin L → ℕ} (C : RootedCycleCollection R L m) :
    collectionOfAssignment (assignmentOfCollection C) = C := by
  have hc : (collectionOfAssignment (assignmentOfCollection C)).1 = C.1 := by
    funext ell
    apply Function.Embedding.ext
    intro a
    apply Subtype.ext
    change periodicOrbit (R : α → α) (C.2 ell a).val = (C.1 ell a).val
    exact periodicOrbit_eq_of_mem_cycleOrbit R ell.val _ (C.1 ell a).property _
      (C.2 ell a).property
  apply Sigma.ext hc
  apply Function.hfunext rfl
  intro ell ell' hell
  have hell' := eq_of_heq hell
  subst ell'
  apply Function.hfunext rfl
  intro a b hab
  have hab' := eq_of_heq hab
  subst b
  apply (Subtype.heq_iff_coe_eq (fun x => ?_)).mpr
  · rfl
  · rw [hc]

/-- The full bijection used in the factorial moment expansion: labelled,
globally distinct vertices satisfying one prescribed block permutation are
exactly ordered actual cycles with one root chosen in each cycle. -/
def rootedCollectionEquivAssignment (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :
    RootedCycleCollection R L m ≃ CycleAssignment R L m where
  toFun := assignmentOfCollection
  invFun := collectionOfAssignment
  left_inv := collectionOfAssignment_assignmentOfCollection
  right_inv := assignmentOfCollection_collectionOfAssignment

/-- The vertex domain has precisely r = sum ell*m_ell elements, without
choosing an arbitrary enumeration or changing the assignment permutation. -/
theorem cycleVertex_card (L : ℕ) (m : Fin L → ℕ) :
    Nat.card (CycleVertex L m) = ∑ ell : Fin L, (ell.val + 1) * m ell := by
  rw [Nat.card_eq_fintype_card]
  simp [CycleVertex, CycleSlot, Fintype.card_sigma, Fintype.sum_sigma, Nat.mul_comm]

/-- Exact labelled-assignment count, with all rotational multiplicities and
falling factorials retained, including zero multiplicities and empty domains. -/
theorem cycleAssignment_card (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :
    Nat.card (CycleAssignment R L m) =
      (∏ ell : Fin L, (cycleCount R ell.val).descFactorial (m ell)) *
        ∏ ell : Fin L, (ell.val + 1) ^ m ell := by
  rw [← Nat.card_congr (rootedCollectionEquivAssignment R L m)]
  exact rootedCycleCollection_card R L m

/-- The rotational divisor is positive, so division cannot conceal a zero
denominator in the factorial-moment identity. -/
theorem cycleAssignment_rootFactor_pos (L : ℕ) (m : Fin L → ℕ) :
    0 < ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell := by
  apply Finset.prod_pos
  intro ell _
  exact pow_pos (Nat.cast_pos.mpr (Nat.succ_pos ell.val)) _

/-- The unrestricted deterministic factorial identity underlying source
1281–1284. The source's additional vertex cutoff is supplied by
`Section5CycleCutoff`, using this equivalence. -/
theorem cycle_factorial_eq_assignment_card (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) :
    (∏ ell : Fin L, ((cycleCount R ell.val).descFactorial (m ell) : ℝ)) =
      (Nat.card (CycleAssignment R L m) : ℝ) /
        ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell := by
  rw [cycleAssignment_card, Nat.cast_mul]
  simp only [Nat.cast_prod, Nat.cast_pow]
  exact (mul_div_cancel_right₀ _ (ne_of_gt (cycleAssignment_rootFactor_pos L m))).symm

/-- The literal product of the assignment indicators in every labelled block. -/
def cycleBlockIndicator (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ)
    (t : CycleVertex L m ↪ α) : ℝ :=
  ∏ x, if R (t x) = t (cycleBlockPermutation L m x) then 1 else 0

theorem sum_cycleBlockIndicator (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :
    (∑ t : CycleVertex L m ↪ α, cycleBlockIndicator R L m t) =
      (Nat.card (CycleAssignment R L m) : ℝ) := by
  classical
  simp only [cycleBlockIndicator, Fintype.prod_boole, Finset.sum_boole]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The unrestricted expansion into distinct labelled assignment indicators,
with exactly the product of rotational divisors. The cutoff expansion used
by the source is proved in `Section5CycleCutoff`. -/
theorem cycle_factorial_eq_assignment_sum (R : Equiv.Perm α) (L : ℕ)
    (m : Fin L → ℕ) :
    (∏ ell : Fin L, ((cycleCount R ell.val).descFactorial (m ell) : ℝ)) =
      (∑ t : CycleVertex L m ↪ α, cycleBlockIndicator R L m t) /
        ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell := by
  rw [sum_cycleBlockIndicator]
  exact cycle_factorial_eq_assignment_card R L m

end Finite
end Luce.Section5
