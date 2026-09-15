import Luce.Model
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.SplitIfs

/-!
# Section 5: rooted directed cycles and their multiplicity

The length is written `k + 1`, so all positive lengths, including fixed points,
are represented. An embedding is exactly the distinct-label condition in
`fixed_points.tex:164–170`. The direction of each edge is the rank map's
direction. `Function.periodicOrbit` is mathlib's cycle modulo rotation, so
singleton cycles are retained.
-/

namespace Luce.Section5

open Function

variable {α : Type*}

/-- The closed directed assignment in equation (cycle-counts), with a root. -/
def IsRootedCycle (R : Equiv.Perm α) (k : ℕ) (t : Fin (k + 1) ↪ α) : Prop :=
  (∀ a : Fin k, R (t a.castSucc) = t a.succ) ∧ R (t (Fin.last k)) = t 0

instance [DecidableEq α] (R : Equiv.Perm α) (k : ℕ) (t : Fin (k + 1) ↪ α) :
    Decidable (IsRootedCycle R k t) :=
  inferInstanceAs (Decidable
    ((∀ a : Fin k, R (t a.castSucc) = t a.succ) ∧ R (t (Fin.last k)) = t 0))

/-- A tuple of distinct labels satisfying all the cycle assignments. -/
abbrev RootedCycle (R : Equiv.Perm α) (k : ℕ) :=
  {t : Fin (k + 1) ↪ α // IsRootedCycle R k t}

/-- The directed assignments determine every entry from the chosen root. -/
theorem rootedCycle_eq_iterate {R : Equiv.Perm α} {k : ℕ}
    (t : RootedCycle R k) (a : Fin (k + 1)) :
    t.1 a = (R : α → α)^[a.val] (t.1 0) := by
  induction a using Fin.induction with
  | zero => rfl
  | succ a ih =>
      rw [← t.2.1 a, ih]
      exact (Function.iterate_succ_apply' _ _ _).symm

theorem rootedCycle_isPeriodicPt {R : Equiv.Perm α} {k : ℕ}
    (t : RootedCycle R k) :
    IsPeriodicPt (R : α → α) (k + 1) (t.1 0) := by
  change (R : α → α)^[k + 1] (t.1 0) = t.1 0
  rw [Function.iterate_succ_apply']
  have he := rootedCycle_eq_iterate t (Fin.last k)
  change t.1 (Fin.last k) = (R : α → α)^[k] (t.1 0) at he
  rw [← he]
  exact t.2.2

/-- Distinctness excludes every smaller positive period; no proper divisor
is counted as a cycle of length `k + 1`. -/
theorem rootedCycle_minimalPeriod {R : Equiv.Perm α} {k : ℕ}
    (t : RootedCycle R k) :
    minimalPeriod (R : α → α) (t.1 0) = k + 1 := by
  have hp := rootedCycle_isPeriodicPt t
  have hle := hp.minimalPeriod_le (Nat.succ_pos k)
  have hpos := hp.minimalPeriod_pos (Nat.succ_pos k)
  apply Nat.le_antisymm hle
  by_contra hn
  have hlt : minimalPeriod (R : α → α) (t.1 0) < k + 1 := by omega
  let a : Fin (k + 1) := ⟨_, hlt⟩
  have he : t.1 a = t.1 0 := by
    rw [rootedCycle_eq_iterate]
    exact iterate_minimalPeriod
  have ha := congrArg Fin.val (t.1.injective he)
  dsimp [a] at ha
  omega

/-- Enumerate the actual orbit of a point of minimal period `k + 1`. -/
noncomputable def rootedCycleOfPeriodicPoint (R : Equiv.Perm α) (k : ℕ)
    (x : {x : α // minimalPeriod (R : α → α) x = k + 1}) : RootedCycle R k := by
  refine ⟨⟨fun a => (R : α → α)^[a.val] x.1, ?_⟩, ?_, ?_⟩
  · intro a b hab
    apply Fin.ext
    exact iterate_injOn_Iio_minimalPeriod (by simpa [x.2] using a.isLt)
      (by simpa [x.2] using b.isLt) hab
  · intro a
    exact (Function.iterate_succ_apply' _ _ _).symm
  · change R ((R : α → α)^[k] x.1) = x.1
    rw [← Function.iterate_succ_apply' (R : α → α) k x.1]
    simpa only [x.2] using (iterate_minimalPeriod (f := (R : α → α)) (x := x.1))

/-- The exact correspondence between the paper's directed tuples and vertices
in cycles of the specified length (`fixed_points.tex:164–170, 303–304`). -/
noncomputable def rootedCycleEquivPeriodicPoint (R : Equiv.Perm α) (k : ℕ) :
    RootedCycle R k ≃ {x : α // minimalPeriod (R : α → α) x = k + 1} where
  toFun t := ⟨t.1 0, rootedCycle_minimalPeriod t⟩
  invFun := rootedCycleOfPeriodicPoint R k
  left_inv t := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro a
    exact (rootedCycle_eq_iterate t a).symm
  right_inv x := by
    apply Subtype.ext
    rfl

section Counting

variable [Fintype α] [DecidableEq α]

/-- The vertices whose actual orbit has the specified positive length. -/
noncomputable def cycleVertices (R : Equiv.Perm α) (k : ℕ) : Finset α := by
  classical
  exact Finset.univ.filter (fun x => minimalPeriod (R : α → α) x = k + 1)

/-- Actual directed cycles, as mathlib's lists modulo rotation. -/
noncomputable def cycleOrbits (R : Equiv.Perm α) (k : ℕ) : Finset (Cycle α) := by
  classical
  exact (cycleVertices R k).image (periodicOrbit (R : α → α))

/-- Number of unrooted cycles, including singleton fixed points. -/
noncomputable def cycleCount (R : Equiv.Perm α) (k : ℕ) : ℕ :=
  (cycleOrbits R k).card

omit [Fintype α] in
theorem mem_periodicOrbit_toFinset (R : Equiv.Perm α) (x y : α) :
    y ∈ (periodicOrbit (R : α → α) x).toFinset ↔
      y ∈ periodicOrbit (R : α → α) x := by
  simp only [periodicOrbit, Cycle.coe_toFinset, List.mem_toFinset, Cycle.mem_coe_iff]

omit [Fintype α] in
theorem periodicOrbit_toFinset_card (R : Equiv.Perm α) (x : α) :
    (periodicOrbit (R : α → α) x).toFinset.card = minimalPeriod (R : α → α) x := by
  rw [periodicOrbit, Cycle.coe_toFinset,
    List.toFinset_card_of_nodup (show
      ((List.range (minimalPeriod (R : α → α) x)).map
        (fun n => (R : α → α)^[n] x)).Nodup from nodup_periodicOrbit)]
  simp

/-- Exactly the vertices of one orbit give that rotation class. -/
theorem cycleOrbit_fiber (R : Equiv.Perm α) (k : ℕ) (x : α)
    (hx : minimalPeriod (R : α → α) x = k + 1) :
    ((cycleVertices R k).filter (fun y =>
      periodicOrbit (R : α → α) y = periodicOrbit (R : α → α) x)) =
      (periodicOrbit (R : α → α) x).toFinset := by
  classical
  have hxp : x ∈ periodicPts (R : α → α) :=
    minimalPeriod_pos_iff_mem_periodicPts.mp (by omega)
  ext y
  simp only [Finset.mem_filter, cycleVertices, Finset.mem_univ, true_and,
    mem_periodicOrbit_toFinset]
  constructor
  · rintro ⟨hy, he⟩
    have hyp : y ∈ periodicPts (R : α → α) :=
      minimalPeriod_pos_iff_mem_periodicPts.mp (by omega)
    rw [← he]
    exact self_mem_periodicOrbit hyp
  · intro hy
    obtain ⟨m, rfl⟩ := (mem_periodicOrbit_iff hxp).mp hy
    exact ⟨(minimalPeriod_apply_iterate hxp m).trans hx,
      periodicOrbit_apply_iterate_eq hxp m⟩

/-- Each cycle has exactly `k + 1` possible roots. This proves the symmetry
factor asserted at `fixed_points.tex:303–304`; no factorial is omitted. -/
theorem cycleVertices_card (R : Equiv.Perm α) (k : ℕ) :
    (cycleVertices R k).card = (k + 1) * cycleCount R k := by
  classical
  rw [Finset.card_eq_sum_card_image (periodicOrbit (R : α → α))]
  change (∑ c ∈ cycleOrbits R k,
    ((cycleVertices R k).filter (fun x => periodicOrbit (R : α → α) x = c)).card) = _
  calc
    _ = ∑ _c ∈ cycleOrbits R k, (k + 1) := by
      apply Finset.sum_congr rfl
      intro c hc
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      have hx' : minimalPeriod (R : α → α) x = k + 1 :=
        (Finset.mem_filter.mp hx).2
      rw [cycleOrbit_fiber R k x hx', periodicOrbit_toFinset_card, hx']
    _ = (k + 1) * cycleCount R k := by simp [cycleCount, Nat.mul_comm]

/-- Rooted tuples count vertices rather than unrooted cycles. -/
theorem rootedCycle_card (R : Equiv.Perm α) (k : ℕ) :
    Nat.card (RootedCycle R k) = (k + 1) * cycleCount R k := by
  classical
  rw [Nat.card_congr (rootedCycleEquivPeriodicPoint R k), Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]
  exact cycleVertices_card R k

/-- The product of the directed edge indicators in equation (cycle-counts). -/
noncomputable def cycleAssignmentWeight (R : Equiv.Perm α) (k : ℕ)
    (t : Fin (k + 1) ↪ α) : ℝ :=
  (∏ a : Fin k, if R (t a.castSucc) = t a.succ then 1 else 0) *
    (if R (t (Fin.last k)) = t 0 then 1 else 0)

omit [Fintype α] in
theorem cycleAssignmentWeight_eq_indicator (R : Equiv.Perm α) (k : ℕ)
    (t : Fin (k + 1) ↪ α) :
    cycleAssignmentWeight R k t = if IsRootedCycle R k t then 1 else 0 := by
  classical
  rw [cycleAssignmentWeight, Fintype.prod_boole]
  simp only [IsRootedCycle]
  split_ifs <;> simp_all

/-- The full distinct-tuple sum in the paper really is the number of roots. -/
theorem sum_cycleAssignmentWeight (R : Equiv.Perm α) (k : ℕ) :
    (∑ t : Fin (k + 1) ↪ α, cycleAssignmentWeight R k t) =
      (Nat.card (RootedCycle R k) : ℝ) := by
  classical
  simp only [cycleAssignmentWeight_eq_indicator, Finset.sum_boole]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The paper's positive divisor is legitimate, and recovers the integer
number of cycles from the directed-tuple count. -/
theorem cycleCount_eq_div_rootedCycle_card (R : Equiv.Perm α) (k : ℕ) :
    (cycleCount R k : ℝ) =
      (1 / (k + 1 : ℝ)) * (Nat.card (RootedCycle R k) : ℝ) := by
  rw [rootedCycle_card]
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, one_div, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) zero_lt_one)),
    one_mul]

/-- Exact source-to-Lean correspondence for equation (cycle-counts), including
the factor `1 / (k + 1)` and the singleton case. -/
theorem cycleCount_eq_tuple_sum (R : Equiv.Perm α) (k : ℕ) :
    (cycleCount R k : ℝ) = (1 / (k + 1 : ℝ)) *
      ∑ t : Fin (k + 1) ↪ α, cycleAssignmentWeight R k t := by
  rw [sum_cycleAssignmentWeight, cycleCount_eq_div_rootedCycle_card]

omit [Fintype α] [DecidableEq α] in
theorem minimalPeriod_symm (R : Equiv.Perm α) (x : α) :
    minimalPeriod (R.symm : α → α) x = minimalPeriod (R : α → α) x := by
  apply minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change (R.symm : α → α)^[n] x = x ↔ (R : α → α)^[n] x = x
  rw [← Equiv.Perm.coe_pow, ← Equiv.Perm.coe_pow]
  change (R⁻¹ ^ n) x = x ↔ (R ^ n) x = x
  rw [inv_pow]
  exact (Equiv.symm_apply_eq (R ^ n)).trans eq_comm

/-- The draw order and rank permutation have the same cycle counts, as stated
at `fixed_points.tex:171–172`; inversion reverses the directed edges. -/
theorem cycleCount_symm (R : Equiv.Perm α) (k : ℕ) :
    cycleCount R.symm k = cycleCount R k := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k)
  rw [← cycleVertices_card, ← cycleVertices_card]
  congr 1
  ext x
  simp [cycleVertices, minimalPeriod_symm]

/-- Length one is exactly the fixed-point count, including empty permutations. -/
theorem cycleCount_zero (R : Equiv.Perm α) :
    cycleCount R 0 = (Finset.univ.filter (fun x => R x = x)).card := by
  have hc := cycleVertices_card R 0
  simpa [cycleVertices, minimalPeriod_eq_one_iff_isFixedPt, IsFixedPt] using hc.symm

theorem cycleCount_eq_fixedCount {n : ℕ} (R : Equiv.Perm (Fin n)) :
    cycleCount R 0 = Luce.fixedCount R :=
  cycleCount_zero R

/-- Cycles longer than the ambient permutation do not exist. -/
theorem cycleCount_eq_zero_of_card_lt (R : Equiv.Perm α) (k : ℕ)
    (hk : Fintype.card α < k + 1) : cycleCount R k = 0 := by
  classical
  have hv : cycleVertices R k = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    have hle := minimalPeriod_le_card (f := (R : α → α)) (x := x)
    omega
  have hmul : (k + 1) * cycleCount R k = 0 := by
    rw [← cycleVertices_card, hv, Finset.card_empty]
  exact (mul_eq_zero.mp hmul).resolve_left (Nat.succ_ne_zero k)

theorem cycleOrbit_length (R : Equiv.Perm α) (k : ℕ) (c : Cycle α)
    (hc : c ∈ cycleOrbits R k) : c.length = k + 1 := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
  exact periodicOrbit_length.trans (Finset.mem_filter.mp hx).2

theorem cycleOrbit_card (R : Equiv.Perm α) (k : ℕ) (c : Cycle α)
    (hc : c ∈ cycleOrbits R k) : c.toFinset.card = k + 1 := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
  exact (periodicOrbit_toFinset_card R x).trans (Finset.mem_filter.mp hx).2

/-- Distinct actual permutation cycles have no common vertex, the essential
disjointness in the factorial expansion at `fixed_points.tex:1281–1284`. -/
theorem cycleOrbits_disjoint (R : Equiv.Perm α) (k j : ℕ) (c d : Cycle α)
    (hc : c ∈ cycleOrbits R k) (hd : d ∈ cycleOrbits R j) (hne : c ≠ d) :
    Disjoint c.toFinset d.toFinset := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hd
  have hxp : x ∈ periodicPts (R : α → α) :=
    minimalPeriod_pos_iff_mem_periodicPts.mp (by
      have hh := (Finset.mem_filter.mp hx).2
      omega)
  have hyp : y ∈ periodicPts (R : α → α) :=
    minimalPeriod_pos_iff_mem_periodicPts.mp (by
      have hh := (Finset.mem_filter.mp hy).2
      omega)
  apply Finset.disjoint_left.mpr
  intro z hzx hzy
  obtain ⟨a, ha⟩ := (mem_periodicOrbit_iff hxp).mp
    ((mem_periodicOrbit_toFinset R x z).mp hzx)
  obtain ⟨b, hb⟩ := (mem_periodicOrbit_iff hyp).mp
    ((mem_periodicOrbit_toFinset R y z).mp hzy)
  apply hne
  calc
    periodicOrbit (R : α → α) x = periodicOrbit (R : α → α) z := by
      rw [← ha, periodicOrbit_apply_iterate_eq hxp a]
    _ = periodicOrbit (R : α → α) y := by
      rw [← hb, periodicOrbit_apply_iterate_eq hyp b]

/-- For each length, an ordered list of pairwise different actual cycles.
`m = 0` gives the empty list, as required for falling factorial moments. -/
abbrev CycleCollection (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :=
  (ℓ : Fin L) → (Fin (m ℓ) ↪ ↥(cycleOrbits R ℓ.val))

/-- The joint falling factorial counts exactly ordered collections of cycles.
This is the first equality in the expansion at `fixed_points.tex:1281–1284`. -/
theorem cycleCollection_card (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :
    Nat.card (CycleCollection R L m) =
      ∏ ℓ : Fin L, (cycleCount R ℓ.val).descFactorial (m ℓ) := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [CycleCollection, Fintype.card_pi, cycleCount]

/-- Cycles selected by different slots of an ordered collection are distinct,
also when their lengths differ. -/
theorem CycleCollection.distinct {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : CycleCollection R L m) (ℓ j : Fin L) (a : Fin (m ℓ)) (b : Fin (m j))
    (hne : (⟨ℓ, a⟩ : Σ i : Fin L, Fin (m i)) ≠ ⟨j, b⟩) :
    (C ℓ a).val ≠ (C j b).val := by
  intro he
  have hl := cycleOrbit_length R ℓ.val _ (C ℓ a).property
  have hj := cycleOrbit_length R j.val _ (C j b).property
  have hℓj : ℓ = j := by
    apply Fin.ext
    rw [he] at hl
    omega
  subst j
  have hab := (C ℓ).injective (Subtype.ext he)
  subst b
  exact hne rfl

/-- Thus every collection counted by the joint falling factorial is genuinely
vertex-disjoint; injectivity restrictions have not been dropped. -/
theorem CycleCollection.disjoint {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : CycleCollection R L m) (ℓ j : Fin L) (a : Fin (m ℓ)) (b : Fin (m j))
    (hne : (⟨ℓ, a⟩ : Σ i : Fin L, Fin (m i)) ≠ ⟨j, b⟩) :
    Disjoint (C ℓ a).val.toFinset (C j b).val.toFinset :=
  cycleOrbits_disjoint R ℓ.val j.val _ _ (C ℓ a).property (C j b).property
    (C.distinct ℓ j a b hne)

/-- One chosen vertex, or root, in every cycle in a collection. -/
abbrev CycleRoots {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : CycleCollection R L m) :=
  (ℓ : Fin L) → (a : Fin (m ℓ)) → ↥((C ℓ a).val.toFinset)

/-- Rooting an ordered collection has precisely the paper's product of
rotation factors, even when some multiplicities or `L` are zero. -/
theorem cycleRoots_card {R : Equiv.Perm α} {L : ℕ} {m : Fin L → ℕ}
    (C : CycleCollection R L m) :
    Nat.card (CycleRoots C) = ∏ ℓ : Fin L, (ℓ.val + 1) ^ m ℓ := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro ℓ _
  rw [Fintype.card_pi]
  calc
    _ = ∏ _a : Fin (m ℓ), (ℓ.val + 1) := by
      apply Finset.prod_congr rfl
      intro a _
      rw [Fintype.card_coe]
      exact cycleOrbit_card R ℓ.val _ (C ℓ a).property
    _ = (ℓ.val + 1) ^ m ℓ := by simp

/-- An ordered cycle collection together with one root in each cycle. -/
abbrev RootedCycleCollection (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :=
  Σ C : CycleCollection R L m, CycleRoots C

/-- The full root multiplicity in the joint factorial expansion: the factor
is `∏ ell, ell ^ m_ell`, with no additional factorial from ordering cycles. -/
theorem rootedCycleCollection_card (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :
    Nat.card (RootedCycleCollection R L m) =
      (∏ ℓ : Fin L, (cycleCount R ℓ.val).descFactorial (m ℓ)) *
        ∏ ℓ : Fin L, (ℓ.val + 1) ^ m ℓ := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hf (C : CycleCollection R L m) :
      Fintype.card (CycleRoots C) = ∏ ℓ : Fin L, (ℓ.val + 1) ^ m ℓ := by
    rw [← Nat.card_eq_fintype_card]
    exact cycleRoots_card C
  simp_rw [hf]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, cycleCollection_card]

end Counting

end Luce.Section5
