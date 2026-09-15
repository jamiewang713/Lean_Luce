import Luce.Section2PointMeasureLaplace
import Luce.Section2CompactLawConvergence

/-! # Weak convergence of laws of actual finite point measures

On a compact spatial space, convergence of Laplace coordinates and eventual
tightness of total counts imply convergence of every bounded continuous
state-test expectation. The sigma algebra is the inherited evaluation sigma
algebra. Literal compactness suffices; no spatial separation or countability
assumption is used.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction NNReal

namespace Luce

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
theorem measurable_pointMeasure_mass :
    Measurable (fun s : FinitePointMeasure X => s.toFiniteMeasure.mass) :=
  ((Measure.measurable_coe MeasurableSet.univ).comp
    FinitePointMeasure.measurable_toMeasure).ennreal_toNNReal

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
theorem pointMeasure_eventually_mass_le (s : FinitePointMeasure X) :
    ∀ᶠ N : ℕ in atTop, s.toFiniteMeasure.mass ≤ N := by
  obtain ⟨m, x, hx⟩ := s.property
  have hm : s.toFiniteMeasure.mass = m := by
    change s.val.mass = m
    rw [← hx]
    exact pointMeasureOfFin_mass x
  filter_upwards [eventually_ge_atTop m] with N hN
  rw [hm]
  exact_mod_cast hN

/-- Every bounded weak-continuous real test is evaluation measurable on the
space of finite point measures, including for arbitrary compact spaces. -/
theorem measurable_boundedContinuous_pointMeasure [CompactSpace X]
    (F : FinitePointMeasure X →ᵇ ℝ) : Measurable F := by
  exact measurable_boundedContinuousFunction_of_compact_exhaustion
    pointMoment isInducing_pointMoment momentLaplaceAlgebra
    momentLaplaceAlgebra_separatesPoints measurable_momentLaplaceAlgebra_pointMoment
    (fun N => {s | s.toFiniteMeasure.mass ≤ N}) FinitePointMeasure.isCompact_mass_le
    pointMeasure_eventually_mass_le F

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- The total-mass tails of any finite law on finite point measures tend to
zero. No expected-mass or regularity hypothesis on the law is needed. -/
theorem pointMeasure_mass_tail_tendsto_zero
    (Q : Measure (FinitePointMeasure X)) [IsFiniteMeasure Q] :
    Tendsto (fun N : ℕ => Q.real {s | (N : ℝ≥0) < s.toFiniteMeasure.mass})
      atTop (𝓝 0) := by
  let E : ℕ → Set (FinitePointMeasure X) :=
    fun N => {s | (N : ℝ≥0) < s.toFiniteMeasure.mass}
  have hEmeas (N : ℕ) : MeasurableSet (E N) :=
    measurableSet_lt measurable_const measurable_pointMeasure_mass
  have hEanti : Antitone E := by
    intro n m hnm s hs
    exact (show (n : ℝ≥0) ≤ m by exact_mod_cast hnm).trans_lt hs
  have hEempty : (⋂ N, E N) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨N, hN⟩ := (pointMeasure_eventually_mass_le s).exists
    exact (not_lt_of_ge hN) (Set.mem_iInter.mp hs N)
  have h := tendsto_measure_iInter_atTop (μ := Q)
    (fun N => (hEmeas N).nullMeasurableSet) hEanti ⟨0, measure_ne_top _ _⟩
  rw [hEempty, measure_empty] at h
  simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

theorem integrable_momentLaplaceAlgebra_pointMoment
    (Q : Measure (FinitePointMeasure X)) [IsFiniteMeasure Q]
    (a : C(PointMomentSpace X, ℝ)) (ha : a ∈ momentLaplaceAlgebra) :
    Integrable (fun s => a (pointMoment s)) Q := by
  obtain ⟨B, hB⟩ := momentLaplaceAlgebra_bounded a ha
  exact Integrable.of_bound
    (measurable_momentLaplaceAlgebra_pointMoment a ha).aestronglyMeasurable B
    (ae_of_all _ (fun s => hB (pointMoment s)))

/-- Products of Laplace coordinates are again coordinates, so convergence
extends to their entire algebra by linearity of the integral. -/
theorem tendsto_integral_momentLaplaceAlgebra
    (μ : ℕ → Measure (FinitePointMeasure X)) (Q : Measure (FinitePointMeasure X))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure Q]
    (hLaplace : ∀ g : X →ᵇ ℝ≥0,
      Tendsto (fun n => ∫ s, momentLaplace g (pointMoment s) ∂μ n)
        atTop (𝓝 (∫ s, momentLaplace g (pointMoment s) ∂Q)))
    (a : C(PointMomentSpace X, ℝ)) (ha : a ∈ momentLaplaceAlgebra) :
    Tendsto (fun n => ∫ s, a (pointMoment s) ∂μ n)
      atTop (𝓝 (∫ s, a (pointMoment s) ∂Q)) := by
  have ha' : a ∈ Submodule.span ℝ (Set.range (momentLaplace (X := X))) := by
    rw [← momentLaplaceAlgebra_eq_span]
    exact ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    exact hLaplace g
  | zero => simp
  | add a b ha hb hca hcb =>
    have haA : a ∈ momentLaplaceAlgebra := by
      change a ∈ (momentLaplaceAlgebra (X := X)).toSubmodule
      rwa [momentLaplaceAlgebra_eq_span]
    have hbA : b ∈ momentLaplaceAlgebra := by
      change b ∈ (momentLaplaceAlgebra (X := X)).toSubmodule
      rwa [momentLaplaceAlgebra_eq_span]
    have hadd (ρ : Measure (FinitePointMeasure X)) [IsProbabilityMeasure ρ] :
        (∫ s, (a + b) (pointMoment s) ∂ρ) =
          (∫ s, a (pointMoment s) ∂ρ) + ∫ s, b (pointMoment s) ∂ρ :=
      integral_add (integrable_momentLaplaceAlgebra_pointMoment ρ a haA)
        (integrable_momentLaplaceAlgebra_pointMoment ρ b hbA)
    simpa only [hadd] using hca.add hcb
  | smul c a _ hca =>
    simpa only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul] using hca.const_mul c

/-- Laplace convergence plus eventual tightness of total counts yields the
full bounded-continuous-test conclusion for laws of finite point measures. -/
theorem pointMeasure_law_convergence_of_laplace [CompactSpace X]
    (μ : ℕ → Measure (FinitePointMeasure X)) (Q : Measure (FinitePointMeasure X))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure Q]
    (hLaplace : ∀ g : X →ᵇ ℝ≥0,
      Tendsto (fun n => ∫ s, momentLaplace g (pointMoment s) ∂μ n)
        atTop (𝓝 (∫ s, momentLaplace g (pointMoment s) ∂Q)))
    (hTight : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ n in atTop,
      (μ n).real {s | (N : ℝ≥0) < s.toFiniteMeasure.mass} < ε)
    (F : FinitePointMeasure X →ᵇ ℝ) :
    Tendsto (fun n => ∫ s, F s ∂μ n) atTop (𝓝 (∫ s, F s ∂Q)) := by
  apply tendsto_integral_boundedContinuousFunction_of_tight_algebra
    μ Q pointMoment isInducing_pointMoment momentLaplaceAlgebra
    momentLaplaceAlgebra_separatesPoints measurable_momentLaplaceAlgebra_pointMoment
    (fun a ha => ?_) (tendsto_integral_momentLaplaceAlgebra μ Q hLaplace)
    (fun N => {s | s.toFiniteMeasure.mass ≤ N}) FinitePointMeasure.isCompact_mass_le
    (fun N => measurableSet_le measurable_pointMeasure_mass measurable_const)
    pointMeasure_eventually_mass_le (fun ε hε => ?_) F
  · obtain ⟨B, hB⟩ := momentLaplaceAlgebra_bounded a ha
    exact ⟨B, fun s => by simpa only [Real.norm_eq_abs] using hB (pointMoment s)⟩
  · obtain ⟨NQ, hNQ⟩ := ((pointMeasure_mass_tail_tendsto_zero Q).eventually
      (gt_mem_nhds hε)).exists
    obtain ⟨Nμ, hNμ⟩ := hTight ε hε
    refine ⟨max NQ Nμ, ?_, ?_⟩
    · apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hNQ.le
      intro s hs
      change (NQ : ℝ≥0) < s.toFiniteMeasure.mass
      have hs' : ((max NQ Nμ : ℕ) : ℝ≥0) < s.toFiniteMeasure.mass := by
        simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] using hs
      exact (show (NQ : ℝ≥0) ≤ (max NQ Nμ : ℕ) by exact_mod_cast le_max_left NQ Nμ).trans_lt hs'
    · filter_upwards [hNμ] with n hn
      apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hn.le
      intro s hs
      change (Nμ : ℝ≥0) < s.toFiniteMeasure.mass
      have hs' : ((max NQ Nμ : ℕ) : ℝ≥0) < s.toFiniteMeasure.mass := by
        simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] using hs
      exact (show (Nμ : ℝ≥0) ≤ (max NQ Nμ : ℕ) by exact_mod_cast le_max_right NQ Nμ).trans_lt hs'

end Luce
