import Luce.Section5MaximumRoot
import Luce.Section5LowCycleProbability

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Actual retained cycles rooted at their largest label. S restricts only
cycle vertices, never the background rates or clocks. -/
def retainedMaximumCycleEvent {n : ℕ} (k : ℕ) (S : Finset (Fin n)) (v : Fin n) :
    Set (Fin n → ℝ) :=
  {e | minimalPeriod (raceRankPermutation e : Fin n → Fin n) v = k+1 ∧
    (∀ u ∈ (periodicOrbit (raceRankPermutation e : Fin n → Fin n) v).toFinset, u ≤ v) ∧
    (periodicOrbit (raceRankPermutation e : Fin n → Fin n) v).toFinset ⊆ S}

theorem retainedMaximumCycleEvent_eq_actual_roots {n : ℕ} (k : ℕ)
    (S : Finset (Fin n)) (v : Fin n) :
    retainedMaximumCycleEvent k S v =
      {e | v ∈ Section5.maximumCycleRoots (raceRankPermutation e) k ∧
        (periodicOrbit (raceRankPermutation e : Fin n → Fin n) v).toFinset ⊆ S} := by
  ext e
  simp only [retainedMaximumCycleEvent, Set.mem_setOf_eq,
    Section5.mem_maximumCycleRoots_iff, and_assoc]

theorem measurableSet_retainedMaximumCycleEvent {n : ℕ} (k : ℕ)
    (S : Finset (Fin n)) (v : Fin n) : MeasurableSet (retainedMaximumCycleEvent k S v) := by
  simpa only [retainedMaximumCycleEvent, Set.preimage, Function.comp_def,
    Set.mem_singleton_iff, eq_iff_iff, iff_true] using
    ((measurable_of_countable (fun R : Fin n → Fin n => minimalPeriod R v = k+1 ∧
      (∀ u ∈ (periodicOrbit R v).toFinset, u ≤ v) ∧ (periodicOrbit R v).toFinset ⊆ S)).comp
      measurable_raceRankPermutation_function) (measurableSet_singleton True)

theorem exists_retained_maximum_cycle_tail {n k : ℕ} (R : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (v : Fin n)
    (hp : minimalPeriod (R : Fin n → Fin n) v = k+1)
    (hmax : ∀ u ∈ (periodicOrbit (R : Fin n → Fin n) v).toFinset, u ≤ v)
    (hS : (periodicOrbit (R : Fin n → Fin n) v).toFinset ⊆ S) :
    ∃ u : Fin k → Fin n, Injective u ∧ (∀ a, u a < v) ∧
      (∀ a, (Fin.cons v u : Fin (k+1) → Fin n) a ∈ S) ∧
      ∀ a, R ((Fin.cons v u : Fin (k+1) → Fin n) a) =
        (Fin.snoc u v : Fin (k+1) → Fin n) a := by
  obtain ⟨u, hu, huv, hass⟩ := exists_cycle_tail_of_minimalPeriod R v hp
  have hi : ∀ a : Fin (k+1), (Fin.cons v u : Fin (k+1) → Fin n) a =
      (R : Fin n → Fin n)^[a.val] v := by
    intro a
    induction a using Fin.induction with
    | zero => rfl
    | succ a ih =>
      have hh := hass a.castSucc
      simp only [Fin.snoc_castSucc] at hh
      rw [Fin.cons_succ, ← hh, ih]
      exact (iterate_succ_apply' _ _ _).symm
  have hmem (a : Fin (k+1)) :
      (Fin.cons v u : Fin (k+1) → Fin n) a ∈ (periodicOrbit (R : Fin n → Fin n) v).toFinset := by
    rw [Section5.mem_periodicOrbit_toFinset, hi]
    exact iterate_mem_periodicOrbit (R.injective.mem_periodicPts v) _
  refine ⟨u, hu, ?_, fun a => hS (hmem a), hass⟩
  intro a
  exact lt_of_le_of_ne (hmax _ (hmem a.succ)) (huv a)

/-- Restricted maximum-root cylinder bound on one common ghost background.
The inequalities u(a) < v remain in the finite sum. -/
theorem retained_maximum_cycle_probability_le_ghost {n : ℕ} (w : Weights n)
    (k : ℕ) (S : Finset (Fin n)) (v : Fin n) :
    (exponentialRace w).real (retainedMaximumCycleEvent k S v) ≤
      ∫ old, ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        Injective u ∧ (∀ a, u a < v) ∧
          ∀ a, (Fin.cons v u : Fin (k+1) → Fin n) a ∈ S),
        ∏ a : Fin (k+1), ghostEntry w (k+1) old
          ((Fin.cons v u : Fin (k+1) → Fin n) a)
          ((Fin.snoc u v : Fin (k+1) → Fin n) a) ∂exponentialRace w := by
  let s := Finset.univ.filter (fun u : Fin k → Fin n =>
    Injective u ∧ (∀ a, u a < v) ∧ ∀ a, (Fin.cons v u : Fin (k+1) → Fin n) a ∈ S)
  let A := fun u : Fin k → Fin n =>
    {e | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) e}
  have hcover : exponentialRace w (retainedMaximumCycleEvent k S v) ≤
      ∑ u ∈ s, exponentialRace w (A u) := by
    apply (measure_mono_ae (t := ⋃ u ∈ s, A u) ?_).trans (measure_biUnion_finset_le s A)
    filter_upwards [exponentialRace_injective_ae w] with e he
    intro h
    obtain ⟨u, hu, huv, hS, hass⟩ := exists_retained_maximum_cycle_tail
      (raceRankPermutation e) S v h.1 h.2.1 h.2.2
    apply Set.mem_iUnion.mpr
    refine ⟨u, Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, huv, hS⟩, ?_⟩⟩
    intro a
    have hh := congrArg Fin.val (hass a)
    rw [raceRankPermutation_eq e he] at hh
    change clockBeforeCount e (e ((Fin.cons v u : Fin (k+1) → Fin n) a)) =
      ((Fin.snoc u v : Fin (k+1) → Fin n) a).val at hh
    change 1 + clockBeforeCount e (e ((Fin.cons v u : Fin (k+1) → Fin n) a)) =
      ((Fin.snoc u v : Fin (k+1) → Fin n) a).val+1
    omega
  have hreal : (exponentialRace w).real (retainedMaximumCycleEvent k S v) ≤
      ∑ u ∈ s, (exponentialRace w).real (A u) := by
    have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top _ _)) hcover
    rwa [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at h
  calc
    _ ≤ ∑ u ∈ s, (exponentialRace w).real (A u) := hreal
    _ ≤ ∑ u ∈ s, ∫ old, ∏ a : Fin (k+1), ghostEntry w (k+1) old
        ((Fin.cons v u : Fin (k+1) → Fin n) a)
        ((Fin.snoc u v : Fin (k+1) → Fin n) a) ∂exponentialRace w := by
      apply Finset.sum_le_sum
      intro u hu
      have hh := (Finset.mem_filter.mp hu).2
      apply ghost_cylinder_bound
      apply Fin.cons_injective_iff.mpr
      exact ⟨by rintro ⟨a, ha⟩; exact (ne_of_lt (hh.2.1 a)) ha, hh.1⟩
    _ = _ := by
      symm
      exact integral_finsetSum s (fun u _ => ghost_cylinder_product_integrable w _ _)

end Luce
