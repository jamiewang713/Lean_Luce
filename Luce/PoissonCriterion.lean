import Luce.SpatialPoissonLaplace
import Luce.PointMeasureLawConvergence
import Luce.BernoulliCountTightness

/-! # Lemma 2.1: the predictable Poisson criterion

Source: `fixed_points.tex`, `lem:predictable-poisson`,
`eq:poisson-criterion`. The statement is recorded before its proof in
`proposals/Section2PoissonCriterion.md`.

Compactness has its literal open-cover meaning. The conclusion tests the
law against every bounded continuous function of the actual finite point
measure. Measurability of these tests and tightness of the counts are
derived in the proof.
-/

open MeasureTheory Filter Topology
open scoped NNReal BoundedContinuousFunction BigOperators

namespace Luce

/-- The full finite-row predictable Poisson random-measure criterion.
No independence between observations, deterministic probability caps,
or spatial separation/countability assumptions are imposed. -/
theorem predictable_poisson
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (B : ∀ n, FiniteAdaptedBernoulli (P n) n)
    (x : ∀ n, Fin n → X) (ν : FiniteMeasure X)
    (hweak : WeakMeasureConvergesInProbability P
      (fun n => (B n).predictableMeasure (x n)) ν)
    (hmax : ConvergesInProbability P
      (fun n => (B n).toProcess.rowMaximum n) 0)
    (F : FinitePointMeasure X →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F ((B n).pointMeasure (x n) ω) ∂P n)
      atTop (𝓝 (∫ μ, F μ ∂finitePoissonLaw ν)) := by
  let μ : ℕ → Measure (FinitePointMeasure X) :=
    fun n => (P n).map ((B n).pointMeasure (x n))
  have hΞ (n : ℕ) : Measurable ((B n).pointMeasure (x n)) :=
    (B n).measurable_pointMeasure (x n)
  have (n : ℕ) : IsProbabilityMeasure (μ n) :=
    Measure.isProbabilityMeasure_map (hΞ n).aemeasurable
  have hLaplace (g : X →ᵇ ℝ≥0) :
      Tendsto (fun n => ∫ s, momentLaplace g (pointMoment s) ∂μ n)
        atTop (𝓝 (∫ s, momentLaplace g (pointMoment s) ∂finitePoissonLaw ν)) := by
    simp_rw [momentLaplace_pointMoment_eq_pointLaplace]
    have hg : Measurable (fun y : X => (g y : ℝ)) :=
      (NNReal.continuous_coe.comp g.continuous).measurable
    have heq (n : ℕ) :
        (∫ s, pointLaplace (fun y => (g y : ℝ)) s ∂μ n) =
          ∫ ω, pointLaplace (fun y => (g y : ℝ)) ((B n).pointMeasure (x n) ω) ∂P n :=
      integral_map_of_stronglyMeasurable (hΞ n)
        (measurable_pointLaplace _ hg (fun y => (g y).coe_nonneg)).stronglyMeasurable
    simp_rw [heq]
    exact pointMeasure_laplace_tendsto P B x ν hweak hmax g
  have hCount := BernoulliProcess.count_tightness_rows P
    (fun n => (B n).toProcess) id ν.mass.coe_nonneg
    (totalPredictable_tendsto P B x ν hweak) hmax
  have hTight : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ n in atTop,
      (μ n).real {s | (N : ℝ≥0) < s.toFiniteMeasure.mass} < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hCount ε hε
    refine ⟨N, ?_⟩
    filter_upwards [hN] with n hn
    change ((P n).map _).real _ < ε
    rw [map_measureReal_apply (hΞ n)
      (measurableSet_lt measurable_const measurable_pointMeasure_mass)]
    convert hn using 1
    congr 1
    ext ω
    change (N : ℝ≥0) < ((B n).pointMeasure (x n) ω).toFiniteMeasure.mass ↔ _
    rw [← NNReal.coe_lt_coe]
    simp only [NNReal.coe_natCast, FiniteAdaptedBernoulli.pointMeasure_mass,
      id_eq, Set.mem_setOf_eq]
  have h := pointMeasure_law_convergence_of_laplace μ (finitePoissonLaw ν)
    hLaplace hTight F
  have heq (n : ℕ) : (∫ s, F s ∂μ n) =
      ∫ ω, F ((B n).pointMeasure (x n) ω) ∂P n :=
    integral_map_of_stronglyMeasurable (hΞ n)
      (measurable_boundedContinuous_pointMeasure F).stronglyMeasurable
  simpa only [heq] using h

end Luce
