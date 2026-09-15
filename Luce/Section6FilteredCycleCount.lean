import Luce.Section6MaximumRootExcursion

noncomputable section
open Function
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- Filtering literal unrooted cycles by any condition on their maximum
and orbit is exactly filtering their unique maximum roots. -/
theorem filtered_cycle_count_eq_root_count {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (P : Fin n → Cycle (Fin n) → Prop) :
    (Finset.univ.filter (fun c : ↥(Section5.cycleOrbits R k) =>
      P (Section5.cycleMaximum R k c) c.val)).card =
      ((Section5.maximumCycleRoots R k).filter (fun v =>
        P v (periodicOrbit (R : Fin n → Fin n) v))).card := by
  classical
  have he : ((Section5.maximumCycleRoots R k).filter (fun v =>
        P v (periodicOrbit (R : Fin n → Fin n) v))) =
      (Finset.univ.filter (fun c : ↥(Section5.cycleOrbits R k) =>
        P (Section5.cycleMaximum R k c) c.val)).image (Section5.cycleMaximum R k) := by
    ext v
    constructor
    · intro hv
      obtain ⟨hc, hp⟩ := Finset.mem_filter.mp hv
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hc
      rw [Section5.cycleMaximum_orbit] at hp
      exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
    · intro hv
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, ?_⟩
      rw [Section5.cycleMaximum_orbit]
      exact (Finset.mem_filter.mp hc).2
  rw [he, Finset.card_image_of_injective _ (Section5.cycleMaximum_injective R k)]

/-- The actual filtered cycle count is the sum of root indicators.
This applies in particular to the manuscript's discarded-cycle condition. -/
theorem filtered_cycle_count_eq_indicator_sum {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (P : Fin n → Cycle (Fin n) → Prop) :
    (Finset.univ.filter (fun c : ↥(Section5.cycleOrbits R k) =>
      P (Section5.cycleMaximum R k c) c.val)).card =
      ∑ v : Fin n, if v ∈ Section5.maximumCycleRoots R k ∧
        P v (periodicOrbit (R : Fin n → Fin n) v) then 1 else 0 := by
  rw [filtered_cycle_count_eq_root_count]
  have he : ((Section5.maximumCycleRoots R k).filter (fun v =>
      P v (periodicOrbit (R : Fin n → Fin n) v))) =
      Finset.univ.filter (fun v => v ∈ Section5.maximumCycleRoots R k ∧
        P v (periodicOrbit (R : Fin n → Fin n) v)) := by
    ext v
    simp
  rw [he]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Expectation of the literal filtered cycle count is the finite sum of
the actual root-event probabilities. Measurability follows from the finite
permutation space, so no regularity condition on P is assumed. -/
theorem filtered_cycle_expectation_eq_probability_sum {n : ℕ} (w : Weights n)
    (k : ℕ) (P : Fin n → Cycle (Fin n) → Prop) :
    (∫ clocks, ((Finset.univ.filter (fun c : ↥(Section5.cycleOrbits (raceRankPermutation clocks) k) =>
      P (Section5.cycleMaximum (raceRankPermutation clocks) k c) c.val)).card : ℝ)
      ∂exponentialRace w) =
      ∑ v : Fin n, (exponentialRace w).real {clocks |
        v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k ∧
        P v (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v)} := by
  classical
  let E := fun v : Fin n => {clocks : Fin n → ℝ |
    v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k ∧
    P v (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v)}
  have hm (v : Fin n) : MeasurableSet (E v) := by
    have hF : Measurable (fun clocks : Fin n → ℝ => if clocks ∈ E v then (1 : ℕ) else 0) :=
      measurable_race_permutation_statistic (fun R => if v ∈ Section5.maximumCycleRoots R k ∧
        P v (periodicOrbit (R : Fin n → Fin n) v) then (1 : ℕ) else 0)
    simpa using
      measurableSet_eq_fun hF (measurable_const (a := (1 : ℕ)))
  have hi (v : Fin n) : Integrable (fun clocks => if clocks ∈ E v then (1 : ℝ) else 0)
      (exponentialRace w) := by
    have hmeas : Measurable (fun clocks : Fin n → ℝ => if clocks ∈ E v then (1 : ℝ) else 0) :=
      measurable_race_permutation_statistic (fun R => if v ∈ Section5.maximumCycleRoots R k ∧
        P v (periodicOrbit (R : Fin n → Fin n) v) then (1 : ℝ) else 0)
    apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with clocks
    by_cases hc : clocks ∈ E v <;> simp [hc]
  have he (clocks : Fin n → ℝ) :
      ((Finset.univ.filter (fun c : ↥(Section5.cycleOrbits (raceRankPermutation clocks) k) =>
        P (Section5.cycleMaximum (raceRankPermutation clocks) k c) c.val)).card : ℝ) =
      ∑ v : Fin n, if clocks ∈ E v then (1 : ℝ) else 0 := by
    exact_mod_cast filtered_cycle_count_eq_indicator_sum (raceRankPermutation clocks) k P
  simp_rw [he]
  rw [integral_finsetSum _ (fun v _ => hi v)]
  apply Finset.sum_congr rfl
  intro v hv
  simpa only [Set.indicator_apply, smul_eq_mul, mul_one] using
    integral_indicator_const (μ := exponentialRace w) (1 : ℝ) (hm v)

end Luce.Section6
