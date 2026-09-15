import Luce.Section5CycleAssignments
import Luce.Section6CycleVertexBound

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators ENNReal
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- An orbit leaving a set has a nonroot marked vertex in its directed
tuple. This retains the actual permutation and its minimal cycle length. -/
theorem exists_escaping_cycle_tail {n k : ℕ} (R : Equiv.Perm (Fin n))
    (v : Fin n) (P : Fin n → Prop) (hv : ¬ P v)
    (hperiod : minimalPeriod (R : Fin n → Fin n) v = k+1)
    (hescape : ∃ z ∈ (periodicOrbit (R : Fin n → Fin n) v).toFinset, P z) :
    ∃ u : Fin k → Fin n, Injective u ∧ (∀ a, u a ≠ v) ∧ (∃ a, P (u a)) ∧
      ∀ a : Fin (k+1), R ((Fin.cons v u : Fin (k+1) → Fin n) a) =
        (Fin.snoc u v : Fin (k+1) → Fin n) a := by
  let t := Section5.rootedCycleOfPeriodicPoint R k ⟨v, hperiod⟩
  have ht0 : t.val 0 = v := rfl
  let u : Fin k → Fin n := fun a => t.val a.succ
  have hu : Injective u := by
    intro a b hab
    exact Fin.succ_injective _ (t.val.injective hab)
  have huv : ∀ a, u a ≠ v := by
    intro a he
    have hh : t.val a.succ = t.val 0 := by simpa only [ht0] using he
    exact Fin.succ_ne_zero a (t.val.injective hh)
  have hcons : (Fin.cons v u : Fin (k+1) → Fin n) = t.val := by
    funext a
    refine Fin.cases ?_ (fun b => ?_) a
    · simpa only [Fin.cons_zero] using ht0.symm
    · simp only [Fin.cons_succ, u]
  have he : ∃ a, P (u a) := by
    obtain ⟨z, hz, hpz⟩ := hescape
    have hz' : z ∈ periodicOrbit (R : Fin n → Fin n) (t.val 0) :=
      (Section5.mem_periodicOrbit_toFinset R v z).mp hz
    obtain ⟨a, ha⟩ := (Section5.rootedCycle_mem_periodicOrbit_iff t z).mp hz'
    have hpa : P (t.val a) := ha ▸ hpz
    revert hpa
    refine Fin.cases ?_ (fun b hb => ?_) a
    · intro h
      exact (hv h).elim
    · exact ⟨b, hb⟩
  refine ⟨u, hu, huv, he, ?_⟩
  intro a
  rw [hcons]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simpa only [Fin.snoc_last, ht0] using t.property.2
  · simpa only [Fin.snoc_castSucc, u] using t.property.1 b

/-- A finite cylinder union bound retaining the escaping-vertex condition. -/
theorem escaping_cycle_probability_le_cylinders {n k : ℕ} (w : Weights n)
    (v : Fin n) (P : Fin n → Prop) (hv : ¬ P v) :
    (exponentialRace w).real {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1 ∧
      ∃ z ∈ (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v).toFinset, P z} ≤
      ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        Injective u ∧ (∀ a, u a ≠ v) ∧ ∃ a, P (u a)),
        (exponentialRace w).real {clocks |
          MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks} := by
  classical
  let s := Finset.univ.filter (fun u : Fin k → Fin n =>
    Injective u ∧ (∀ a, u a ≠ v) ∧ ∃ a, P (u a))
  let A := fun u : Fin k → Fin n =>
    {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks}
  have hb : exponentialRace w {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1 ∧
      ∃ z ∈ (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v).toFinset, P z} ≤
      ∑ u ∈ s, exponentialRace w (A u) := by
    apply le_trans _ (measure_biUnion_finset_le s A)
    apply measure_mono_ae
    filter_upwards [exponentialRace_injective_ae w] with clocks hc
    rintro ⟨hperiod, hescape⟩
    obtain ⟨u, hu, huv, he, hassign⟩ :=
      exists_escaping_cycle_tail (raceRankPermutation clocks) v P hv hperiod hescape
    refine Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, huv, he⟩, ?_⟩⟩
    intro a
    rw [raceRankPermutation_eq clocks hc] at hassign
    have h := congrArg Fin.val (hassign a)
    change clockBeforeCount clocks (clocks ((Fin.cons v u : Fin (k+1) → Fin n) a)) =
      ((Fin.snoc u v : Fin (k+1) → Fin n) a).val at h
    change 1 + clockBeforeCount clocks (clocks ((Fin.cons v u : Fin (k+1) → Fin n) a)) =
      ((Fin.snoc u v : Fin (k+1) → Fin n) a).val+1
    omega
  have ht := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top _ _)) hb
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at ht
  exact ht

/-- Closing the escaping path costs only the target maximum at its root.
The escape restriction is preserved when distinctness is dropped. -/
theorem escaping_cycle_probability_le_paths {n k r : ℕ} (w : Weights n)
    (hkr : k+1 ≤ r) (v : Fin n) (P : Fin n → Prop) (hv : ¬ P v)
    {T : ℝ} (hT : 0 ≤ T)
    (htarget : ∀ i, insertionDominationMatrix w r r i v ≤ T) :
    (exponentialRace w).real {clocks |
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1 ∧
      ∃ z ∈ (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v).toFinset, P z} ≤
      T * ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n => ∃ a, P (u a)),
        forwardPathWeight (insertionDominationMatrix w r r) v u := by
  classical
  let M := insertionDominationMatrix w r r
  let s := Finset.univ.filter (fun u : Fin k → Fin n =>
    Injective u ∧ (∀ a, u a ≠ v) ∧ ∃ a, P (u a))
  let t := Finset.univ.filter (fun u : Fin k → Fin n => ∃ a, P (u a))
  have hcylinder : ∀ u ∈ s,
      (exponentialRace w).real {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks} ≤
        T*forwardPathWeight M v u := by
    intro u hu
    obtain ⟨huinj, huv, he⟩ := (Finset.mem_filter.mp hu).2
    have hvnot : v ∉ Set.range u := by rintro ⟨a, ha⟩; exact huv a ha
    have ht := markedRankCylinder_real_probability_le_domination_matrix w hkr
      (Fin.cons v u) (Fin.snoc u v)
      (Fin.cons_injective_iff.mpr ⟨hvnot, huinj⟩)
      (Fin.snoc_injective_iff.mpr ⟨huinj, hvnot⟩)
    have hid : (∏ a : Fin (k+1), M ((Fin.cons v u : Fin (k+1) → Fin n) a)
        ((Fin.snoc u v : Fin (k+1) → Fin n) a)) =
        forwardPathWeight M v u * M ((Fin.cons v u : Fin (k+1) → Fin n) (Fin.last k)) v := by
      simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, forwardPathWeight]
    change _ ≤ ∏ a : Fin (k+1), M ((Fin.cons v u : Fin (k+1) → Fin n) a)
      ((Fin.snoc u v : Fin (k+1) → Fin n) a) at ht
    rw [hid] at ht
    exact ht.trans (by
      rw [mul_comm T]
      exact mul_le_mul_of_nonneg_left (htarget _)
        (Finset.prod_nonneg (fun a _ => insertionDominationMatrix_nonneg w r r _ _)))
  calc
    _ ≤ ∑ u ∈ s, (exponentialRace w).real
        {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks} :=
      escaping_cycle_probability_le_cylinders w v P hv
    _ ≤ ∑ u ∈ s, T*forwardPathWeight M v u := Finset.sum_le_sum hcylinder
    _ ≤ ∑ u ∈ t, T*forwardPathWeight M v u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro u hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.2.2⟩
      · intro u hu hnot
        exact mul_nonneg hT (Finset.prod_nonneg
          (fun a _ => insertionDominationMatrix_nonneg w r r _ _))
    _ = _ := (Finset.mul_sum _ _ _).symm

end Luce.Section6
