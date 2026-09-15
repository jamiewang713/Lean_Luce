import Luce.PoissonCriterion

/-!
# The predictable Poisson criterion in its tested-integral form

For `fixed_points.tex:816–818`, Proposition 3.2 supplies convergence of every
continuous compensator integral. This file reuses the checked likelihood,
tightness, and Laplace-to-law proof of Lemma 2.1 directly with those tests.
It does not assume convergence of the main compensator or the Poisson law.
-/

open MeasureTheory Filter Topology
open scoped NNReal BoundedContinuousFunction BigOperators

namespace Luce

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
  (B : ∀ n, FiniteAdaptedBernoulli (P n) n)
  (x : ∀ n, Fin n → X) (ν : FiniteMeasure X)

theorem totalPredictable_of_integrals
    (htest : ∀ g : X →ᵇ ℝ, ConvergesInProbability P
      (fun n ω => ∫ y, g y ∂((B n).predictableMeasure (x n) ω : Measure X))
      (∫ y, g y ∂(ν : Measure X))) :
    ConvergesInProbability P
      (fun n ω => ∑ k ∈ Finset.range n, (B n).toProcess.probability k ω)
      (ν.mass : ℝ) := by
  have hone (a : FiniteMeasure X) :
      (∫ y, (1 : X →ᵇ ℝ) y ∂(a : Measure X)) = (a.mass : ℝ) := by
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply,
      integral_const, smul_eq_mul, mul_one]
    rfl
  simpa only [hone, FiniteAdaptedBernoulli.predictableMeasure_mass] using htest 1

theorem pointMeasure_laplace_of_integrals
    (htest : ∀ g : X →ᵇ ℝ, ConvergesInProbability P
      (fun n ω => ∫ y, g y ∂((B n).predictableMeasure (x n) ω : Measure X))
      (∫ y, g y ∂(ν : Measure X)))
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
    convert htest q using 1
    funext n ω
    exact (B n).laplaceCompensator_eq_integral_predictableMeasure (x n) gR hg ω
  have h := BernoulliProcess.uncapped_laplace_tendsto_rows P
    (fun n => (B n).toProcess)
    (fun n => FiniteAdaptedBernoulli.spatialTest (x n) gR) (fun n => n)
    ν.mass.coe_nonneg hlam
    (fun n => FiniteAdaptedBernoulli.spatialTest_nonneg (x n) gR hg0)
    (totalPredictable_of_integrals P B x ν htest) hmax hcomp
  rw [integral_pointLaplace_finitePoissonLaw ν (fun z => (g z : ℝ)) hg hg0]
  change Tendsto (fun n => ∫ ω, pointLaplace gR ((B n).pointMeasure (x n) ω) ∂P n)
    atTop (𝓝 (Real.exp (-lam)))
  convert h using 1
  funext n
  exact integral_congr_ae (ae_of_all _ (fun ω =>
    (B n).pointLaplace_pointMeasure (x n) gR hg ω))

/-- The full law conclusion of Lemma 2.1, with its compensator assumption
supplied one continuous test at a time by Proposition 3.2. -/
theorem predictable_poisson_of_integrals
    (htest : ∀ g : X →ᵇ ℝ, ConvergesInProbability P
      (fun n ω => ∫ y, g y ∂((B n).predictableMeasure (x n) ω : Measure X))
      (∫ y, g y ∂(ν : Measure X)))
    (hmax : ConvergesInProbability P (fun n => (B n).toProcess.rowMaximum n) 0)
    (F : FinitePointMeasure X →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F ((B n).pointMeasure (x n) ω) ∂P n)
      atTop (𝓝 (∫ μ, F μ ∂finitePoissonLaw ν)) := by
  let μ : ℕ → Measure (FinitePointMeasure X) :=
    fun n => (P n).map ((B n).pointMeasure (x n))
  have hΞ (n : ℕ) : Measurable ((B n).pointMeasure (x n)) :=
    (B n).measurable_pointMeasure (x n)
  haveI (n : ℕ) : IsProbabilityMeasure (μ n) :=
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
    exact pointMeasure_laplace_of_integrals P B x ν htest hmax g
  have hCount := BernoulliProcess.count_tightness_rows P
    (fun n => (B n).toProcess) id ν.mass.coe_nonneg
    (totalPredictable_of_integrals P B x ν htest) hmax
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
      id_eq, Set.mem_ofPred_eq]
  have h := pointMeasure_law_convergence_of_laplace μ (finitePoissonLaw ν) hLaplace hTight F
  have heq (n : ℕ) : (∫ s, F s ∂μ n) = ∫ ω, F ((B n).pointMeasure (x n) ω) ∂P n :=
    integral_map_of_stronglyMeasurable (hΞ n)
      (measurable_boundedContinuous_pointMeasure F).stronglyMeasurable
  simpa only [heq] using h

end Luce
