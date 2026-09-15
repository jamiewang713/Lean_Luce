import Luce.FiniteBernoulliSpatial
import Luce.WeakMeasureProbability
import Luce.UncappedPoisson

/-! # Spatial Laplace limits from predictable measure convergence

The weak-neighborhood hypothesis supplies the constant test and the tested
compensator `1 - exp (-g)`. The uncapped scalar theorem then gives the
Laplace functional of the finite-intensity Poisson law.
-/

open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction NNReal

namespace Luce

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [CompactSpace X]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
  (B : ∀ n, FiniteAdaptedBernoulli (P n) n) (x : ∀ n, Fin n → X)
  (ν : FiniteMeasure X)

omit [CompactSpace X] in
/-- The total predictable mass converges in probability by applying the
weak-measure hypothesis to the constant-one spatial test. -/
theorem totalPredictable_tendsto
    (hweak : WeakMeasureConvergesInProbability P
      (fun n => (B n).predictableMeasure (x n)) ν) :
    ConvergesInProbability P
      (fun n ω => ∑ k ∈ Finset.range n, (B n).toProcess.probability k ω)
      (ν.mass : ℝ) := by
  have hone (a : FiniteMeasure X) :
      (∫ z, (1 : X →ᵇ ℝ) z ∂(a : Measure X)) = (a.mass : ℝ) := by
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply,
      integral_const, smul_eq_mul, mul_one]
    rfl
  simpa only [hone, FiniteAdaptedBernoulli.predictableMeasure_mass] using
    hweak.integral (1 : X →ᵇ ℝ)

/-- Under the manuscript's weak predictable-measure and vanishing-maximum
hypotheses, each nonnegative continuous spatial Laplace test converges to
the corresponding test under the constructed finite Poisson law. -/
theorem pointMeasure_laplace_tendsto
    (hweak : WeakMeasureConvergesInProbability P
      (fun n => (B n).predictableMeasure (x n)) ν)
    (hmax : ConvergesInProbability P (fun n => (B n).toProcess.rowMaximum n) 0)
    (g : X →ᵇ ℝ≥0) :
    Tendsto (fun n => ∫ ω,
      pointLaplace (fun z => (g z : ℝ)) ((B n).pointMeasure (x n) ω) ∂P n)
      atTop (𝓝 (∫ s, pointLaplace (fun z => (g z : ℝ)) s ∂finitePoissonLaw ν)) := by
  let gR : X → ℝ := fun z => (g z : ℝ)
  have hg : Measurable gR := (NNReal.continuous_coe.comp g.continuous).measurable
  have hg0 (z : X) : 0 ≤ gR z := (g z).coe_nonneg
  let q : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun z => 1 - Real.exp (-gR z),
      continuous_const.sub (Real.continuous_exp.comp
        (NNReal.continuous_coe.comp g.continuous).neg)⟩
  let lam : ℝ := ∫ z, q z ∂(ν : Measure X)
  have hlam : 0 ≤ lam := integral_nonneg (fun z => by
    change 0 ≤ 1 - Real.exp (-gR z)
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg0 z))))
  have hcomp : ConvergesInProbability P
      (fun n => (B n).toProcess.laplaceCompensator
        (FiniteAdaptedBernoulli.spatialTest (x n) gR) n) lam := by
    convert hweak.integral q using 1
    funext n ω
    exact (B n).laplaceCompensator_eq_integral_predictableMeasure (x n) gR hg ω
  have h := BernoulliProcess.uncapped_laplace_tendsto_rows P
    (fun n => (B n).toProcess)
    (fun n => FiniteAdaptedBernoulli.spatialTest (x n) gR) (fun n => n)
    ν.mass.coe_nonneg hlam
    (fun n => FiniteAdaptedBernoulli.spatialTest_nonneg (x n) gR hg0)
    (totalPredictable_tendsto P B x ν hweak) hmax hcomp
  rw [integral_pointLaplace_finitePoissonLaw ν (fun z => (g z : ℝ)) hg hg0]
  change Tendsto (fun n => ∫ ω, pointLaplace gR ((B n).pointMeasure (x n) ω) ∂P n)
    atTop (𝓝 (Real.exp (-lam)))
  convert h using 1
  funext n
  exact integral_congr_ae (ae_of_all _ (fun ω =>
    (B n).pointLaplace_pointMeasure (x n) gR hg ω))

end Luce
