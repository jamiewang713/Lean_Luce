import Luce.Section5GhostCylinder
import Luce.Section5Cycles

/-!
# Bounding the cycle probability at a fixed vertex

The rooted-cycle correspondence is used to sum the ghost cylinder estimate
over exactly the distinct tails avoiding the specified root. This is the
finite cycle comparison used in the exceptional-rate estimates of Section 5.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

/-- Total rank permutation. On the null set of tied clock configurations
it is extended by the identity; on distinct clocks it is the actual rank map. -/
def raceRankPermutation {n : ℕ} (clocks : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  if h : Function.Injective clocks then rankPermutation clocks h else Equiv.refl _

lemma raceRankPermutation_eq {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) :
    raceRankPermutation clocks = rankPermutation clocks hinj := by
  simp only [raceRankPermutation, hinj, dite_true]

lemma section5_measurableSet_injective_clocks (n : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ | Function.Injective clocks} := by
  change MeasurableSet {clocks : Fin n → ℝ | ∀ i j, clocks i = clocks j → i = j}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  · simp [hij]
  · have hm : MeasurableSet {clocks : Fin n → ℝ | clocks i = clocks j} :=
      measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
    convert hm.compl using 1
    ext clocks
    simp [hij]

lemma measurable_raceRankPermutation_apply {n : ℕ} (i : Fin n) :
    Measurable (fun clocks : Fin n → ℝ => raceRankPermutation clocks i) := by
  apply measurable_to_countable'
  intro k
  have heq : (fun clocks : Fin n → ℝ => raceRankPermutation clocks i) ⁻¹' {k} =
      ({clocks | Function.Injective clocks} ∩
        {clocks | clockBeforeCount clocks (clocks i) = k.val}) ∪
      ({clocks | ¬ Function.Injective clocks} ∩ {clocks : Fin n → ℝ | i = k}) := by
    ext clocks
    by_cases hi : Function.Injective clocks
    · simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
        Set.mem_ofPred_eq, hi, true_and, not_true_eq_false, false_and, or_false]
      rw [raceRankPermutation_eq clocks hi]
      change clockRank clocks i = k ↔ (clockRank clocks i).val = k.val
      exact Fin.ext_iff
    · simp [raceRankPermutation, hi]
  rw [heq]
  have hc := measurable_clockBeforeCount (fun c : Fin n → ℝ => c)
    (fun c => c i) (fun j => measurable_pi_apply j) (measurable_pi_apply i)
  exact ((section5_measurableSet_injective_clocks n).inter
    (measurableSet_eq_fun hc measurable_const)).union
      ((section5_measurableSet_injective_clocks n).compl.inter (by measurability))

lemma measurable_raceRankPermutation_function {n : ℕ} :
    Measurable (fun clocks : Fin n → ℝ => (raceRankPermutation clocks : Fin n → Fin n)) :=
  measurable_pi_iff.mpr measurable_raceRankPermutation_apply

lemma measurableSet_cycle_period {n : ℕ} (v : Fin n) (k : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1} :=
  measurableSet_eq_fun
    ((measurable_of_countable (fun R : Fin n → Fin n => minimalPeriod R v)).comp
      measurable_raceRankPermutation_function) measurable_const

/-- A vertex with minimal period `k+1` has a directed tuple with that root,
with `k` distinct remaining vertices avoiding it. The endpoint is the root. -/
theorem exists_cycle_tail_of_minimalPeriod {n k : ℕ} (R : Equiv.Perm (Fin n))
    (v : Fin n) (hperiod : minimalPeriod (R : Fin n → Fin n) v = k + 1) :
    ∃ u : Fin k → Fin n, Function.Injective u ∧ (∀ a, u a ≠ v) ∧
      ∀ a : Fin (k + 1), R ((Fin.cons v u : Fin (k + 1) → Fin n) a) =
        (Fin.snoc u v : Fin (k + 1) → Fin n) a := by
  let t := Section5.rootedCycleOfPeriodicPoint R k ⟨v, hperiod⟩
  have ht0 : t.val 0 = v := rfl
  let u : Fin k → Fin n := fun a => t.val a.succ
  have hu : Function.Injective u := by
    intro a b hab
    exact Fin.succ_injective _ (t.val.injective hab)
  have huv : ∀ a, u a ≠ v := by
    intro a he
    have hh : t.val a.succ = t.val 0 := by simpa only [ht0] using he
    exact Fin.succ_ne_zero a (t.val.injective hh)
  have hcons : (Fin.cons v u : Fin (k + 1) → Fin n) = t.val := by
    funext a
    refine Fin.cases ?_ (fun b => ?_) a
    · simpa only [Fin.cons_zero] using ht0.symm
    · simp only [Fin.cons_succ, u]
  refine ⟨u, hu, huv, ?_⟩
  intro a
  rw [hcons]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simpa only [Fin.snoc_last, ht0] using t.property.2
  · simpa only [Fin.snoc_castSucc, u] using t.property.1 b

/-- On distinct clock configurations, the cycle tuple satisfies the exact
one-based rank assignments required by the ghost cylinder inequality. -/
theorem cycle_period_has_rankCylinder {n k : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (v : Fin n)
    (hperiod : minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1) :
    ∃ u : Fin k → Fin n, Function.Injective u ∧ (∀ a, u a ≠ v) ∧
      MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks := by
  rw [raceRankPermutation_eq clocks hinj] at hperiod
  obtain ⟨u, hu, huv, hassign⟩ := exists_cycle_tail_of_minimalPeriod
    (rankPermutation clocks hinj) v hperiod
  refine ⟨u, hu, huv, ?_⟩
  intro a
  have he := congrArg Fin.val (hassign a)
  change clockBeforeCount clocks (clocks ((Fin.cons v u : Fin (k + 1) → Fin n) a)) =
    ((Fin.snoc u v : Fin (k + 1) → Fin n) a).val at he
  change 1 + clockBeforeCount clocks (clocks ((Fin.cons v u : Fin (k + 1) → Fin n) a)) =
    ((Fin.snoc u v : Fin (k + 1) → Fin n) a).val + 1
  omega

/-- The cycle event is covered by precisely the admissible rooted cylinders.
The finite union bound introduces no rotation or factorial multiplicity. -/
theorem cycle_period_probability_le_sum_cylinders {n k : ℕ} (w : Weights n)
    (v : Fin n) :
    exponentialRace w {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1} ≤
      ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        exponentialRace w {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks} := by
  let s := Finset.univ.filter (fun u : Fin k → Fin n =>
    Function.Injective u ∧ ∀ a, u a ≠ v)
  let A := fun u : Fin k → Fin n =>
    {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks}
  calc
    _ ≤ exponentialRace w (⋃ u ∈ s, A u) := by
      apply measure_mono_ae
      filter_upwards [exponentialRace_injective_ae w] with clocks hc
      intro hp
      obtain ⟨u, hu, huv, hr⟩ := cycle_period_has_rankCylinder clocks hc v hp
      exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, huv⟩, hr⟩⟩
    _ ≤ _ := measure_biUnion_finset_le s A

lemma cycle_period_real_probability_le_sum_cylinders {n k : ℕ} (w : Weights n)
    (v : Fin n) :
    (exponentialRace w).real {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1} ≤
      ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        (exponentialRace w).real
          {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks} := by
  have hf : (∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
      Function.Injective u ∧ ∀ a, u a ≠ v),
      exponentialRace w {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks}) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top _ _)
  have h := (ENNReal.toReal_le_toReal (measure_ne_top _ _) hf).mpr
    (cycle_period_probability_le_sum_cylinders (k := k) w v)
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at h
  exact h

/-- The source's rooted cycle sum: first edge out of `v`, followed by a
distinct-source path ending at `v`. For `k=0` this is exactly `p_(v,v)`. -/
def ghostCycleVertexSum {n : ℕ} (w : Weights n) (k : ℕ)
    (v : Fin n) (old : Fin n → ℝ) : ℝ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
      Function.Injective u ∧ ∀ a, u a ≠ v),
    ghostEntry w (k + 1) old v ((Fin.snoc u v : Fin (k + 1) → Fin n) 0) *
      ∏ a : Fin k, ghostEntry w (k + 1) old (u a)
        ((Fin.snoc u v : Fin (k + 1) → Fin n) a.succ)

lemma ghostCycleVertexSum_eq_cylinder_sum {n : ℕ} (w : Weights n) (k : ℕ)
    (v : Fin n) (old : Fin n → ℝ) :
    ghostCycleVertexSum w k v old =
      ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        ∏ a : Fin (k + 1), ghostEntry w (k + 1) old
          ((Fin.cons v u : Fin (k + 1) → Fin n) a)
          ((Fin.snoc u v : Fin (k + 1) → Fin n) a) := by
  simp only [ghostCycleVertexSum, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Every cycle-probability majorant is integrable before its expectation
is used. Its finitely many summands are products of probabilities. -/
theorem ghostCycleVertexSum_integrable {n : ℕ} (w : Weights n) (k : ℕ)
    (v : Fin n) : Integrable (ghostCycleVertexSum w k v) (exponentialRace w) := by
  change Integrable (fun old => ghostCycleVertexSum w k v old) (exponentialRace w)
  simp_rw [ghostCycleVertexSum_eq_cylinder_sum]
  apply integrable_finsetSum
  intro u _
  exact ghost_cylinder_product_integrable w (Fin.cons v u) (Fin.snoc u v)

/-- The exact finite vertex-cycle comparison used in the high- and low-rate
proofs: the cycle probability is bounded by the expected rooted ghost sum.
There is no symmetry factor because the root is fixed. -/
theorem cycle_vertex_probability_le_ghost {n : ℕ} (w : Weights n) (k : ℕ)
    (v : Fin n) :
    (exponentialRace w).real {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1} ≤
      ∫ old, ghostCycleVertexSum w k v old ∂exponentialRace w := by
  calc
    _ ≤ ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        (exponentialRace w).real
          {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks} :=
      cycle_period_real_probability_le_sum_cylinders w v
    _ ≤ ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        ∫ old, ∏ a : Fin (k + 1), ghostEntry w (k + 1) old
          ((Fin.cons v u : Fin (k + 1) → Fin n) a)
          ((Fin.snoc u v : Fin (k + 1) → Fin n) a) ∂exponentialRace w := by
      apply Finset.sum_le_sum
      intro u hu
      have hu' := (Finset.mem_filter.mp hu).2
      apply ghost_cylinder_bound
      apply Fin.cons_injective_iff.mpr
      refine ⟨?_, hu'.1⟩
      rintro ⟨a, ha⟩
      exact hu'.2 a ha
    _ = _ := by
      simp_rw [ghostCycleVertexSum_eq_cylinder_sum]
      symm
      apply integral_finsetSum
      intro u _
      exact ghost_cylinder_product_integrable w (Fin.cons v u) (Fin.snoc u v)

end Luce
