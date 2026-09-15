import Luce.Section5BulkPointMass
import Luce.Section5ContractDefinitions

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators Topology
namespace Luce

theorem measurable_race_permutation_statistic {n : ℕ} {E : Type*}
    [MeasurableSpace E] (F : Equiv.Perm (Fin n) → E) :
    Measurable (fun z : Fin n → ℝ => F (raceRankPermutation z)) := by
  classical
  let G (g : Fin n → Fin n) :=
    if h : Function.Bijective g then F (Equiv.ofBijective g h) else F (Equiv.refl _)
  have he (z : Fin n → ℝ) : G (raceRankPermutation z : Fin n → Fin n) =
      F (raceRankPermutation z) := by
    dsimp [G]
    rw [dif_pos (raceRankPermutation z).bijective]
    congr 1
    ext i
    rfl
  simpa only [Function.comp_def, he] using
    (measurable_of_countable G).comp measurable_raceRankPermutation_function

def bulkCycleVectorPoissonLaw (f : ℝ → ℝ) (α : ℝ) (L : ℕ) : Measure (Fin L → ℕ) :=
  Measure.pi (fun ell => poissonMeasure (Real.toNNReal (bulkCycleTraceIntensity f α ell.val)))

instance bulkCycleVectorPoissonLaw_probability (f : ℝ → ℝ) (α : ℝ) (L : ℕ) :
    IsProbabilityMeasure (bulkCycleVectorPoissonLaw f α L) := by
  unfold bulkCycleVectorPoissonLaw
  infer_instance

theorem bulk_cycle_point_indicator_integral {n : ℕ} (w : Weights n)
    (L : ℕ) (q : Fin L → ℕ) (α : ℝ) :
    (∫ z, (if (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q
      then (1 : ℝ) else 0) ∂exponentialRace w) =
      (exponentialRace w).real {z | (fun ell =>
        Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q} := by
  classical
  have hF : Measurable (fun z : Fin n → ℝ => fun ell : Fin L =>
      Section5.bulkCycleCount (raceRankPermutation z) α ell.val) :=
    measurable_race_permutation_statistic (fun (R : Equiv.Perm (Fin n)) (ell : Fin L) =>
      Section5.bulkCycleCount R α ell.val)
  have hm : MeasurableSet {z : Fin n → ℝ | (fun ell =>
      Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q} :=
    measurableSet_eq_fun hF measurable_const
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
    integral_indicator_const (μ := exponentialRace w) (1 : ℝ) hm

theorem bulkCycleVectorPoissonLaw_real_singleton (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (L : ℕ)
    (α : ℝ) (hα : α < 1) (q : Fin L → ℕ) :
    (bulkCycleVectorPoissonLaw f α L).real {q} =
      ∏ ell, Real.exp (-bulkCycleTraceIntensity f α ell.val) *
        bulkCycleTraceIntensity f α ell.val ^ q ell / ((q ell).factorial : ℝ) := by
  unfold bulkCycleVectorPoissonLaw
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro ell _
  rw [← measureReal_def, poissonMeasure_real_singleton,
    Real.coe_toNNReal _ (bulk_cycle_intensity_nonneg w f hnorm hf ell.val α hα)]

/-- The actual bulk cycle-vector event probabilities converge to the
unchanged independent-Poisson law determined by the manuscript integrals. -/
theorem bulk_cycle_point_probability_limit (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (q : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => (exponentialRace (w n)).real {z | (fun ell =>
      Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q}) atTop
      (𝓝 ((bulkCycleVectorPoissonLaw f α L).real {q})) := by
  rw [bulkCycleVectorPoissonLaw_real_singleton w f hnorm hf L α hα q]
  have h := bulk_cycle_point_indicator_limit w f hnorm hf L q α hα
  simpa only [bulk_cycle_point_indicator_integral] using h

end Luce
