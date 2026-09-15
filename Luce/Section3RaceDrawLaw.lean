import Luce.Section3RaceLaw
import Luce.Section3Probability
import Mathlib.Order.Preorder.Finite

/-!
# Measurable Luce draw order of the independent exponential race

The sorted-event law is connected to the total permutation `raceDraw` used
in Section 3. The identity value at ties is a measurable extension on an
explicitly proved null event, not an extra hypothesis on the sample space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set

namespace Luce

lemma strictMono_draw_clocks {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) :
    StrictMono (fun k => clocks (drawPermutation clocks hinj k)) := by
  intro j k hjk
  by_contra hnot
  have hle : clocks (drawPermutation clocks hinj k) ≤ arrivalTime clocks hinj j :=
    le_of_not_gt hnot
  have hkj := (draw_arrivalTime_le_iff clocks hinj k j).mp hle
  exact (not_le_of_gt hjk) hkj

/-- The sorted draw permutation is uniquely characterized by increasing
clock times. The finite order comparison proves uniqueness at every index. -/
theorem drawPermutation_eq_iff_strictMono {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (π : Equiv.Perm (Fin n)) :
    drawPermutation clocks hinj = π ↔ StrictMono (fun k => clocks (π k)) := by
  constructor
  · rintro rfl
    exact strictMono_draw_clocks clocks hinj
  · intro hπ
    let d := drawPermutation clocks hinj
    have hcomp : StrictMono (fun k => d.symm (π k)) := by
      intro j k hjk
      by_contra hnot
      have hle : d.symm (π k) ≤ d.symm (π j) := le_of_not_gt hnot
      have hc := (strictMono_draw_clocks clocks hinj).monotone hle
      change clocks (d (d.symm (π k))) ≤ clocks (d (d.symm (π j))) at hc
      simp only [Equiv.apply_symm_apply] at hc
      exact (not_le_of_gt (hπ hjk)) hc
    have hid := hcomp.eq_id
    apply Equiv.ext
    intro k
    have hk := congrFun hid k
    have hdk := congrArg d hk
    simpa only [Function.id_def, Equiv.apply_symm_apply] using hdk.symm

lemma measurableSet_injective_clocks (n : ℕ) :
    MeasurableSet {clocks : Fin n → ℝ | Function.Injective clocks} := by
  classical
  simp only [Function.Injective, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, imp_false]
    have hi : Measurable (fun clocks : Fin n → ℝ => clocks i) := measurable_pi_apply i
    have hj : Measurable (fun clocks : Fin n → ℝ => clocks j) := measurable_pi_apply j
    convert (measurableSet_eq_fun hi hj).compl using 1
    ext clocks
    rfl

/-- The full draw order is measurable into the discrete finite permutation
space, including the exceptional tied-clock configurations. -/
theorem measurable_raceDraw (n : ℕ) :
    @Measurable (Fin n → ℝ) (Equiv.Perm (Fin n)) inferInstance ⊤ raceDraw := by
  classical
  letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  change Measurable (raceDraw : (Fin n → ℝ) → Equiv.Perm (Fin n))
  apply measurable_to_countable'
  intro π
  have hsorted : MeasurableSet {clocks : Fin n → ℝ | StrictMono (fun k => clocks (π k))} :=
    (measurableSet_strictMono_clocks n).preimage
      (measurable_pi_lambda _ (fun k => measurable_pi_apply (π k)))
  have heq : raceDraw ⁻¹' {π} =
      ({clocks : Fin n → ℝ | Function.Injective clocks} ∩
        {clocks | StrictMono (fun k => clocks (π k))}) ∪
      ({clocks | ¬Function.Injective clocks} ∩ {clocks | Equiv.refl (Fin n) = π}) := by
    ext clocks
    by_cases hinj : Function.Injective clocks
    · simp only [Set.mem_preimage, Set.mem_singleton_iff, raceDraw_eq clocks hinj,
        Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, hinj, not_true_eq_false,
        true_and, false_and, or_false]
      exact drawPermutation_eq_iff_strictMono clocks hinj π
    · simp [raceDraw, hinj]
  rw [heq]
  have hconst : MeasurableSet {clocks : Fin n → ℝ | Equiv.refl (Fin n) = π} := by
    by_cases hπ : Equiv.refl (Fin n) = π <;> simp [hπ]
  exact ((measurableSet_injective_clocks n).inter hsorted).union
    ((measurableSet_injective_clocks n).compl.inter hconst)

/-- The total measurable draw permutation has the exact full Luce law. -/
theorem raceDraw_mass {n : ℕ} (w : Weights n) (π : Equiv.Perm (Fin n)) :
    (exponentialRace w).real {clocks | raceDraw clocks = π} = w.mass π := by
  have heq : {clocks : Fin n → ℝ | raceDraw clocks = π} =ᵐ[exponentialRace w]
      {clocks | StrictMono (fun k => clocks (π k))} := by
    filter_upwards [exponentialRace_injective_ae w] with clocks hinj
    apply propext
    change raceDraw clocks = π ↔ StrictMono (fun k => clocks (π k))
    rw [raceDraw_eq clocks hinj]
    exact drawPermutation_eq_iff_strictMono clocks hinj π
  rw [Measure.real, measure_congr heq]
  exact exponentialRace_order_probability w π

end Luce
