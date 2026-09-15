import Luce.FinitePoissonLaw
import Luce.PointMeasureLawConvergence

/-! # Count tightness from Laplace convergence

The extension argument in Section 4 of `fixed_points.tex` needs tightness
without convergence of expected counts. Markov's inequality applied to the
bounded gap `1 - exp (-t X)` gives exactly this implication.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal BoundedContinuousFunction

namespace Luce

/-- Markov's inequality for the bounded Laplace gap, with no first-moment
assumption on the nonnegative random variable. -/
theorem laplace_gap_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    {t : ℝ} (ht : 0 < t) (N : ℕ) (hN : 1 ≤ t * N) :
    (1 - Real.exp (-1)) * P.real {ω | (N : ℝ) < Y ω} ≤
      1 - ∫ ω, Real.exp (-t * Y ω) ∂P := by
  have hi : Integrable (fun ω => Real.exp (-t * Y ω)) P := by
    simpa only [neg_mul] using integrable_exp_neg P (fun ω => t * Y ω)
      (measurable_const.mul hY) (fun ω => mul_nonneg ht.le (hY0 ω))
  have hgap (ω : Ω) : 0 ≤ 1 - Real.exp (-t * Y ω) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [hY0 ω]))
  have hδ : 0 ≤ 1 - Real.exp (-1) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  calc
    _ ≤ (1 - Real.exp (-1)) * P.real {ω | 1 - Real.exp (-1) ≤
        1 - Real.exp (-t * Y ω)} := by
      apply mul_le_mul_of_nonneg_left _ hδ
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      change (N : ℝ) < Y ω at hω
      change 1 - Real.exp (-1) ≤ 1 - Real.exp (-t * Y ω)
      apply sub_le_sub_left
      apply Real.exp_le_exp.mpr
      have := mul_lt_mul_of_pos_left hω ht
      nlinarith
    _ ≤ ∫ ω, 1 - Real.exp (-t * Y ω) ∂P :=
      mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hgap)
        ((integrable_const 1).sub hi) _
    _ = _ := by rw [integral_sub (integrable_const 1) hi]; simp

/-- Laplace convergence to a transform continuous at zero forces eventual
tightness of any row of nonnegative random variables. -/
theorem nonneg_laplace_tightness
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Y : ∀ n, Ω n → ℝ) (hY : ∀ n, Measurable (Y n))
    (hY0 : ∀ n ω, 0 ≤ Y n ω) (L : ℝ → ℝ)
    (hLaplace : ∀ t : ℝ, 0 < t →
      Tendsto (fun n => ∫ ω, Real.exp (-t * Y n ω) ∂P n) atTop (𝓝 (L t)))
    (hL : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ n in atTop,
      (P n).real {ω | (N : ℝ) < Y n ω} < ε := by
  intro ε hε
  let δ : ℝ := 1 - Real.exp (-1)
  have hδ : 0 < δ := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hsmall := (tendsto_const_nhds.sub hL).eventually
    (gt_mem_nhds (show (1 : ℝ) - 1 < ε * δ / 2 by nlinarith))
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hlt⟩ := (hpos.and hsmall).exists
  have ht' : 0 < t := ht
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / t)
  have hNt : 1 ≤ t * N := by
    have := (div_le_iff₀ ht').mp hN
    nlinarith
  refine ⟨N, ?_⟩
  have hrow := (tendsto_const_nhds.sub (hLaplace t ht')).eventually
    (gt_mem_nhds (show 1 - L t < ε * δ by nlinarith))
  filter_upwards [hrow] with n hn
  have hb := laplace_gap_tail_bound (P n) (Y n) (hY n) (hY0 n) ht' N hNt
  change δ * (P n).real {ω | (N : ℝ) < Y n ω} ≤ _ at hb
  nlinarith

/-- The Laplace transform of a proper law of finite nonnegative variables
is right-continuous at zero, independently of its expectation. -/
theorem nonneg_laplace_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) :
    Tendsto (fun t : ℝ => ∫ ω, Real.exp (-t * Y ω) ∂P)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := P) (F := fun t ω => Real.exp (-t * Y ω)) (f := fun _ => (1 : ℝ))
    (l := 𝓝[>] (0 : ℝ)) (fun _ => (1 : ℝ))
    (Eventually.of_forall fun t => (measurable_const.mul hY).exp.aestronglyMeasurable)
    (by filter_upwards [self_mem_nhdsWithin] with t ht
        exact Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_one_iff.mpr
          have ht' : 0 < t := ht
          nlinarith [hY0 ω])
    (integrable_const 1)
    (Eventually.of_forall fun ω => by
      have hc : Continuous (fun t : ℝ => Real.exp (-t * Y ω)) := by fun_prop
      have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa only [neg_zero, zero_mul, Real.exp_zero] using h)
  simpa using h

section PointMeasures

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The constant Laplace coordinate is the ordinary total-mass Laplace test. -/
theorem momentLaplace_const_pointMoment (t : ℝ≥0) (ξ : FinitePointMeasure X) :
    momentLaplace (BoundedContinuousFunction.const X t) (pointMoment ξ) =
      Real.exp (-(t : ℝ) * (ξ.toFiniteMeasure.mass : ℝ)) := by
  rw [momentLaplace_pointMoment_eq_pointLaplace]
  simp only [pointLaplace, BoundedContinuousFunction.const_apply, integral_const,
    smul_eq_mul, FiniteMeasure.measureReal_eq_coe_coeFn]
  congr 1
  change -((ξ.toFiniteMeasure.mass : ℝ) * (t : ℝ)) = _
  ring

/-- Laplace convergence to any probability law on finite point measures
already supplies the total-count tightness required by the law-convergence
theorem. No expected-mass convergence or integrability is assumed. -/
theorem pointMeasure_tightness_of_laplace
    (μ : ℕ → Measure (FinitePointMeasure X)) (Q : Measure (FinitePointMeasure X))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure Q]
    (hLaplace : ∀ g : X →ᵇ ℝ≥0,
      Tendsto (fun n => ∫ ξ, momentLaplace g (pointMoment ξ) ∂μ n) atTop
        (𝓝 (∫ ξ, momentLaplace g (pointMoment ξ) ∂Q))) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ n in atTop,
      (μ n).real {ξ | (N : ℝ≥0) < ξ.toFiniteMeasure.mass} < ε := by
  let Y : FinitePointMeasure X → ℝ := fun ξ => ξ.toFiniteMeasure.mass
  have hY : Measurable Y := measurable_pointMeasure_mass.coe_nnreal_real
  have hY0 : ∀ ξ, 0 ≤ Y ξ := fun ξ => ξ.toFiniteMeasure.mass.coe_nonneg
  have htight := nonneg_laplace_tightness (fun _ => FinitePointMeasure X) μ
    (fun _ => Y) (fun _ => hY) (fun _ => hY0)
    (fun t => ∫ ξ, Real.exp (-t * Y ξ) ∂Q)
    (fun t ht => by
      have hh := hLaplace (BoundedContinuousFunction.const X ⟨t, ht.le⟩)
      have heq (ξ : FinitePointMeasure X) :
          momentLaplace (BoundedContinuousFunction.const X ⟨t, ht.le⟩) (pointMoment ξ) =
            Real.exp (-t * Y ξ) := momentLaplace_const_pointMoment ⟨t, ht.le⟩ ξ
      simpa only [heq] using hh)
    (nonneg_laplace_tendsto_zero Q Y hY hY0)
  have hset (N : ℕ) : {ξ | (N : ℝ) < Y ξ} =
      {ξ : FinitePointMeasure X | (N : ℝ≥0) < ξ.toFiniteMeasure.mass} := by
    ext ξ
    change (((N : ℝ≥0) : ℝ) < (ξ.toFiniteMeasure.mass : ℝ)) ↔ _
    exact NNReal.coe_lt_coe
  simpa only [hset] using htight

end PointMeasures

end Luce
