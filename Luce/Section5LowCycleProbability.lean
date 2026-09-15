import Luce.Section5LowCycleRows
import Luce.Section5ExceptionalInteraction

/-!
# Restricted cycle probabilities in Proposition 5.4

Source: `fixed_points.tex:1225–1230`. The event restricts only the rates
on the actual cycle. The background rates are arbitrary positive rates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function Filter
open scoped BigOperators ENNReal Topology
namespace Luce
attribute [local instance] Classical.propDecidable

def boundedCycleEvent {n : ℕ} (w : Weights n) (k : ℕ) (M : ℝ) (v : Fin n) :
    Set (Fin n → ℝ) :=
  {clocks | minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k + 1 ∧
    OrbitAvoids (raceRankPermutation clocks)
      (Finset.univ.filter (fun i => M < w.rate i)) v}

lemma measurableSet_boundedCycleEvent {n : ℕ} (w : Weights n) (k : ℕ)
    (M : ℝ) (v : Fin n) : MeasurableSet (boundedCycleEvent w k M v) := by
  simpa only [boundedCycleEvent, Set.preimage, Function.comp_def, Set.mem_singleton_iff,
    eq_iff_iff, iff_true] using ((measurable_of_countable (fun R : Fin n → Fin n =>
    minimalPeriod R v = k + 1 ∧ OrbitAvoids R
      (Finset.univ.filter (fun i => M < w.rate i)) v)).comp
      measurable_raceRankPermutation_function) (measurableSet_singleton True)

/-- The rooted tuple supplied by an actual cycle inherits exactly its
vertex restriction. No restriction on any other label is introduced. -/
lemma exists_bounded_cycle_tail {n k : ℕ} (w : Weights n) (R : Equiv.Perm (Fin n))
    (M : ℝ) (v : Fin n) (hp : minimalPeriod (R : Fin n → Fin n) v = k + 1)
    (ha : OrbitAvoids R (Finset.univ.filter (fun i => M < w.rate i)) v) :
    ∃ u : Fin k → Fin n, Injective u ∧ (∀ a, u a ≠ v) ∧
      (∀ a, w.rate ((Fin.cons v u : Fin (k + 1) → Fin n) a) ≤ M) ∧
      ∀ a, R ((Fin.cons v u : Fin (k + 1) → Fin n) a) =
        (Fin.snoc u v : Fin (k + 1) → Fin n) a := by
  obtain ⟨u, hu, huv, hass⟩ := exists_cycle_tail_of_minimalPeriod R v hp
  have hi : ∀ a : Fin (k + 1), (Fin.cons v u : Fin (k + 1) → Fin n) a =
      (R : Fin n → Fin n)^[a.val] v := by
    intro a
    induction a using Fin.induction with
    | zero => rfl
    | succ a ih =>
      have hh := hass a.castSucc
      simp only [Fin.snoc_castSucc] at hh
      rw [Fin.cons_succ, ← hh, ih]
      exact (iterate_succ_apply' _ _ _).symm
  refine ⟨u, hu, huv, ?_, hass⟩
  intro a
  apply le_of_not_gt
  intro h
  apply ha _ ?_ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  rw [hi]
  exact iterate_mem_periodicOrbit (R.injective.mem_periodicPts v) _

/-- The restricted rooted-cylinder union bound, with every selected label
and its original exponential rate retained. -/
theorem bounded_cycle_probability_le_ghost {n : ℕ} (w : Weights n)
    (k : ℕ) (M : ℝ) (v : Fin n) :
    (exponentialRace w).real (boundedCycleEvent w k M v) ≤
      ∫ old, ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        Injective u ∧ (∀ a, u a ≠ v) ∧
          ∀ a, w.rate ((Fin.cons v u : Fin (k + 1) → Fin n) a) ≤ M),
        ∏ a : Fin (k + 1), ghostEntry w (k + 1) old
          ((Fin.cons v u : Fin (k + 1) → Fin n) a)
          ((Fin.snoc u v : Fin (k + 1) → Fin n) a) ∂exponentialRace w := by
  let s := Finset.univ.filter (fun u : Fin k → Fin n =>
    Injective u ∧ (∀ a, u a ≠ v) ∧
      ∀ a, w.rate ((Fin.cons v u : Fin (k + 1) → Fin n) a) ≤ M)
  let A := fun u : Fin k → Fin n =>
    {clocks | MarkedRankCylinder (Fin.cons v u) (Fin.snoc u v) clocks}
  have hcover : exponentialRace w (boundedCycleEvent w k M v) ≤
      ∑ u ∈ s, exponentialRace w (A u) := by
    apply (measure_mono_ae (t := ⋃ u ∈ s, A u) ?_).trans (measure_biUnion_finset_le s A)
    filter_upwards [exponentialRace_injective_ae w] with clocks hc
    intro he
    obtain ⟨u, hu, huv, hM, hass⟩ := exists_bounded_cycle_tail w
      (raceRankPermutation clocks) M v he.1 he.2
    apply Set.mem_iUnion.mpr
    refine ⟨u, Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, huv, hM⟩, ?_⟩⟩
    intro a
    have hh := congrArg Fin.val (hass a)
    rw [raceRankPermutation_eq clocks hc] at hh
    change clockBeforeCount clocks (clocks ((Fin.cons v u : Fin (k + 1) → Fin n) a)) =
      ((Fin.snoc u v : Fin (k + 1) → Fin n) a).val at hh
    change 1 + clockBeforeCount clocks (clocks ((Fin.cons v u : Fin (k + 1) → Fin n) a)) =
      ((Fin.snoc u v : Fin (k + 1) → Fin n) a).val + 1
    omega
  have hreal : (exponentialRace w).real (boundedCycleEvent w k M v) ≤
      ∑ u ∈ s, (exponentialRace w).real (A u) := by
    have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top _ _)) hcover
    rwa [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at h
  calc
    _ ≤ ∑ u ∈ s, (exponentialRace w).real (A u) := hreal
    _ ≤ ∑ u ∈ s, ∫ old, ∏ a : Fin (k + 1), ghostEntry w (k + 1) old
        ((Fin.cons v u : Fin (k + 1) → Fin n) a)
        ((Fin.snoc u v : Fin (k + 1) → Fin n) a) ∂exponentialRace w := by
      apply Finset.sum_le_sum
      intro u hu
      have hh := (Finset.mem_filter.mp hu).2
      apply ghost_cylinder_bound
      apply Fin.cons_injective_iff.mpr
      exact ⟨by rintro ⟨a, ha⟩; exact hh.2.1 a ha, hh.1⟩
    _ = _ := by
      symm
      exact integral_finsetSum s (fun u _ => ghost_cylinder_product_integrable w _ _)

/-- Finite restricted cycle bound after integrating the deterministic row
estimate. Integrability of the actual length is an explicit auxiliary premise
and is discharged from the reservoir in the next theorem. -/
theorem bounded_cycle_probability_le_window {n : ℕ} (w : Weights n)
    (k : ℕ) (M : ℝ) (hM : 0 ≤ M) (v : Fin n) (hv : v.val + (k + 1) < n)
    (hi : Integrable (fun old => ghostWindowLength (k + 1) old v) (exponentialRace w)) :
    (exponentialRace w).real (boundedCycleEvent w k M v) ≤
      (M * (2 * (k + 1) + 1 : ℕ) ^ k) *
        ∫ old, ghostWindowLength (k + 1) old v ∂exponentialRace w := by
  apply (bounded_cycle_probability_le_ghost w k M v).trans
  rw [← integral_const_mul]
  apply integral_mono_ae
    (integrable_finsetSum _ (fun u _ => ghost_cylinder_product_integrable w _ _)) (hi.const_mul _)
  filter_upwards [exponentialRace_nonnegative_background w] with old hold
  have h := bounded_ghost_cycle_sum_le w k M hM old hold v hv
  simpa only [mul_right_comm] using h

/-- Source 1225–1230 with every auxiliary window premise discharged. -/
theorem ProfileLimit.bounded_cycle_probability_uniform {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (L : ℕ) (M : ℝ) (hM : 0 < M)
    {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ v : Fin n,
      (v.val : ℝ) + 1 ≤ α * n → ∀ k : Fin L,
        (exponentialRace (w n)).real (boundedCycleEvent (w n) k.val M v) ≤ K / n := by
  obtain ⟨C, hC, hwin⟩ := hf.interior_ghostWindowLength_uniform L hα
  let B : Fin L → ℝ := fun k => M * (2 * (k.val + 1) + 1 : ℕ) ^ k.val
  have hB (k : Fin L) : 0 ≤ B k := mul_nonneg hM.le (pow_nonneg (Nat.cast_nonneg _) _)
  have hmargin : ∀ᶠ n : ℕ in atTop, (L : ℝ) ≤ (1 - α) * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop ((L : ℝ) / (1 - α)))] with n hn
    simpa only [mul_comm] using (div_le_iff₀ (sub_pos.mpr hα)).mp hn
  refine ⟨(∑ k, B k) * C + 1, by positivity, ?_⟩
  filter_upwards [hwin, hmargin] with n hn hmar v hv k
  have hk : k.val + 1 ≤ L := by omega
  have hidx : v.val + (k.val + 1) < n := by
    have hk' : ((k.val + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hk
    have hh : (v.val : ℝ) + (k.val + 1 : ℕ) < n := by linarith
    exact_mod_cast hh
  obtain ⟨hInt, hbound⟩ := hn (k.val + 1) hk v hv
  calc
    _ ≤ B k * ∫ old, ghostWindowLength (k.val + 1) old v ∂exponentialRace (w n) :=
      bounded_cycle_probability_le_window (w n) k.val M hM.le v hidx hInt
    _ ≤ B k * (C / n) := mul_le_mul_of_nonneg_left hbound (hB k)
    _ = (B k * C) / n := (mul_div_assoc _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (by
      have := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ k)) hC.le
      linarith) (Nat.cast_nonneg n)

/-- The restricted vertex count is a finite sum of the actual short-cycle
events. The positive period of a finite permutation supplies the length
index; the estimate does not omit fixed points. -/
theorem shortCycleVertexCountAvoiding_expectation_le {n : ℕ} (w : Weights n)
    (L : ℕ) (M : ℝ) (S : Finset (Fin n)) :
    (∫ clocks, (shortCycleVertexCountAvoiding (raceRankPermutation clocks) L S
      (Finset.univ.filter (fun i => M < w.rate i)) : ℝ) ∂exponentialRace w) ≤
      ∑ v ∈ S, ∑ k : Fin L, (exponentialRace w).real (boundedCycleEvent w k.val M v) := by
  let H := Finset.univ.filter (fun i => M < w.rate i)
  have heq (clocks : Fin n → ℝ) :
      (shortCycleVertexCountAvoiding (raceRankPermutation clocks) L S H : ℝ) =
      ∑ v ∈ S, if ∃ k : Fin L, clocks ∈ boundedCycleEvent w k.val M v then 1 else 0 := by
    have hiff (v : Fin n) :
        (minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v ≤ L ∧
          OrbitAvoids (raceRankPermutation clocks) H v) ↔
        ∃ k : Fin L, clocks ∈ boundedCycleEvent w k.val M v := by
      have hp := minimalPeriod_pos_of_mem_periodicPts
        ((raceRankPermutation clocks).injective.mem_periodicPts v)
      constructor
      · rintro ⟨hle, ha⟩
        refine ⟨⟨minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v - 1,
          by omega⟩, ?_, ha⟩
        dsimp only
        omega
      · rintro ⟨k, hk, ha⟩
        exact ⟨by rw [hk]; omega, ha⟩
    simp only [shortCycleVertexCountAvoiding, ← Finset.sum_boole, hiff]
  have hm (v : Fin n) : MeasurableSet {clocks | ∃ k : Fin L,
      clocks ∈ boundedCycleEvent w k.val M v} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun k => measurableSet_boundedCycleEvent w k.val M v)
  change (∫ clocks, (shortCycleVertexCountAvoiding (raceRankPermutation clocks) L S H : ℝ)
    ∂exponentialRace w) ≤ _
  simp_rw [heq]
  rw [integral_finsetSum S (fun v _ => by
    apply ((integrable_const (μ := exponentialRace w) (1 : ℝ)).indicator (hm v)).congr
    exact Eventually.of_forall (fun clocks => by
      simp only [Set.indicator_apply, Set.mem_setOf_eq]))]
  apply Finset.sum_le_sum
  intro v _
  have hid := integral_indicator_one (μ := exponentialRace w) (hm v)
  simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] at hid
  rw [hid]
  simp only [Set.ofPred_exists]
  exact measureReal_iUnion_fintype_le _

end Luce
