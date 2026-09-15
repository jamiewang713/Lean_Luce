import Luce.Section3PoissonLaw
import Luce.PointMeasureLawConvergence

/-! # The total-count law in Section 4

For `fixed_points.tex`, the last paragraph of the proof of
`thm:main-poisson`: total mass is a continuous, natural-valued observable
on finite point measures, and its law under the canonical Poisson random
measure is the scalar Poisson law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Luce

variable {X : Type*} [MeasurableSpace X]

/-- Section 4: the total count of a finite Poisson random measure has the
scalar Poisson law with parameter equal to the full intensity mass. -/
theorem finitePoissonLaw_count_univ (ν : FiniteMeasure X) :
    (finitePoissonLaw ν).map (fun ξ => ξ.count Set.univ) = poissonMeasure ν.mass := by
  have h := finitePoissonLaw_count_joint ν 1 (fun _ => Set.univ)
    (fun _ => MeasurableSet.univ) (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
  have hm : Measurable (fun ξ : FinitePointMeasure X => fun _i : Fin 1 => ξ.count Set.univ) :=
    measurable_pi_lambda _ (fun _ => FinitePointMeasure.measurable_count MeasurableSet.univ)
  have hmap := congrArg (Measure.map (Function.eval (0 : Fin 1))) h
  rw [Measure.map_map (measurable_pi_apply (0 : Fin 1)) hm] at hmap
  simpa only [Function.comp_def, Function.eval, FiniteMeasure.mass] using
    hmap.trans (measurePreserving_eval (fun _ : Fin 1 => poissonMeasure (ν Set.univ)) 0).map_eq

section Topology

variable [TopologicalSpace X] [OpensMeasurableSpace X]

/-- Section 4: evaluation on the whole spatial space is continuous even
as a natural-valued observable, because finite point measures have integer mass. -/
theorem FinitePointMeasure.continuous_count_univ :
    Continuous (fun ξ : FinitePointMeasure X => ξ.count Set.univ) := by
  apply Nat.isClosedEmbedding_coe_real.isEmbedding.isInducing.continuous_iff.mpr
  have h : (fun ξ : FinitePointMeasure X => (ξ.count Set.univ : ℝ)) =
      fun ξ => (ξ.toFiniteMeasure.mass : ℝ) := by
    funext ξ
    exact ξ.count_coe_eq MeasurableSet.univ
  change Continuous (fun ξ : FinitePointMeasure X => (ξ.count Set.univ : ℝ))
  rw [h]
  exact continuous_subtype_val.comp
    (FiniteMeasure.continuous_mass.comp FinitePointMeasure.continuous_toFiniteMeasure)

/-- A bounded continuous test for any specified value of the total count. -/
def pointCountSingletonTest (k : ℕ) : FinitePointMeasure X →ᵇ ℝ where
  toFun ξ := if ξ.count Set.univ = k then 1 else 0
  continuous_toFun :=
    (show Continuous (fun n : ℕ => if n = k then (1 : ℝ) else 0) from
      continuous_of_discreteTopology).comp FinitePointMeasure.continuous_count_univ
  map_bounded' := ⟨1, fun ξ ζ => by
    rw [Real.dist_eq]
    split_ifs <;> norm_num⟩

theorem integral_pointCountSingletonTest (Q : Measure (FinitePointMeasure X)) (k : ℕ) :
    (∫ ξ, pointCountSingletonTest k ξ ∂Q) =
      (Q.map (fun ξ => ξ.count Set.univ)).real {k} := by
  have hset : MeasurableSet {ξ : FinitePointMeasure X | ξ.count Set.univ = k} :=
    FinitePointMeasure.measurable_count MeasurableSet.univ (measurableSet_singleton k)
  have heq : (fun ξ : FinitePointMeasure X => pointCountSingletonTest k ξ) =
      {ξ | ξ.count Set.univ = k}.indicator (fun _ => (1 : ℝ)) := by
    funext ξ
    simp only [pointCountSingletonTest, BoundedContinuousFunction.coe_mk,
      Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq, integral_indicator hset, setIntegral_const]
  simp only [smul_eq_mul, mul_one, Measure.real,
    Measure.map_apply (FinitePointMeasure.measurable_count MeasurableSet.univ)
      (measurableSet_singleton k)]
  rfl

theorem integral_pointCountSingletonTest_finitePoissonLaw (ν : FiniteMeasure X) (k : ℕ) :
    (∫ ξ, pointCountSingletonTest k ξ ∂finitePoissonLaw ν) =
      (poissonMeasure ν.mass).real {k} := by
  rw [integral_pointCountSingletonTest, finitePoissonLaw_count_univ]

/-- The singleton test evaluates the count law on any underlying sample space. -/
theorem integral_pointCountSingletonTest_comp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → FinitePointMeasure X) (hZ : Measurable Z) (k : ℕ) :
    (∫ ω, pointCountSingletonTest k (Z ω) ∂P) =
      (P.map (fun ω => (Z ω).count Set.univ)).real {k} := by
  have hF : Measurable (pointCountSingletonTest (X := X) k) := by
    change Measurable (fun ξ : FinitePointMeasure X =>
      if ξ.count Set.univ = k then (1 : ℝ) else 0)
    exact measurable_const.ite
      (measurableSet_eq_fun (FinitePointMeasure.measurable_count MeasurableSet.univ)
        measurable_const) measurable_const
  rw [← integral_map hZ.aemeasurable hF.aestronglyMeasurable,
    integral_pointCountSingletonTest,
    Measure.map_map (FinitePointMeasure.measurable_count MeasurableSet.univ) hZ]
  rfl

/-- Section 4: weak convergence of point-measure laws gives pointwise
convergence of the actual total-count probability mass functions. -/
theorem pointMeasure_count_singleton_tendsto
    (μ : ℕ → Measure (FinitePointMeasure X)) (Q : Measure (FinitePointMeasure X))
    (hWeak : ∀ F : FinitePointMeasure X →ᵇ ℝ,
      Tendsto (fun n => ∫ ξ, F ξ ∂μ n) atTop (𝓝 (∫ ξ, F ξ ∂Q))) (k : ℕ) :
    Tendsto (fun n => ((μ n).map (fun ξ => ξ.count Set.univ)).real {k}) atTop
      (𝓝 ((Q.map (fun ξ => ξ.count Set.univ)).real {k})) := by
  simpa only [integral_pointCountSingletonTest] using hWeak (pointCountSingletonTest k)

/-- Section 4: the total-count probability masses of random finite point
measures converge to scalar Poisson probability masses whenever their spatial
laws converge to the canonical finite Poisson law. -/
theorem pointMeasure_random_count_singleton_poisson_tendsto
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (Z : ∀ n, Ω n → FinitePointMeasure X)
    (hZ : ∀ n, Measurable (Z n)) (ν : FiniteMeasure X)
    (hWeak : ∀ F : FinitePointMeasure X →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (Z n ω) ∂P n) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw ν))) (k : ℕ) :
    Tendsto (fun n => ((P n).map (fun ω => (Z n ω).count Set.univ)).real {k}) atTop
      (𝓝 ((poissonMeasure ν.mass).real {k})) := by
  simpa only [integral_pointCountSingletonTest_comp _ _ (hZ _),
    integral_pointCountSingletonTest_finitePoissonLaw] using hWeak (pointCountSingletonTest k)

end Topology
end Luce
