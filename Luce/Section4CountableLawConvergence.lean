import Luce.Section4CountableTotalVariation

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace Luce.CountableLaw
variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

theorem tendsto_event_probability_of_totalVariation
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (h : Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0)) (A : Set E) :
    Tendsto (fun n => (μ n : Measure E).real A) atTop (𝓝 ((ν : Measure E).real A)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h.eventually (gt_mem_nhds hε)] with n hn
  rw [Real.dist_eq]
  exact (probability_event_difference_le_totalVariation (μ n) ν A).trans_lt hn

theorem tendsto_probabilityMeasure_of_totalVariation
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (h : Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0)) :
    Tendsto μ atTop (𝓝 ν) := by
  apply tendsto_of_forall_isClosed_limsup_real_le'
  intro A _
  exact (tendsto_event_probability_of_totalVariation h A).limsup_eq.le

theorem tendsto_bounded_integrals_of_totalVariation
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (h : Tendsto (fun n => probabilityTotalVariation (μ n) ν) atTop (𝓝 0))
    (F : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, F x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, F x ∂(ν : Measure E))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_probabilityMeasure_of_totalVariation h) F

end Luce.CountableLaw
