import Luce.Section4Intensity
import Luce.FinitePoissonLaw

/-! # The full finite intensity and convergence of its interior restrictions

Source: `fixed_points.tex:947–955`. The representation on the compact unit
interval is the same projection used for the interior intensity in Section 3.
Its finiteness is a consequence of the endpoint argument, not an assumption.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace Luce

/-- The manuscript's full diagonal intensity as a finite measure on [0,1]. -/
def fullIntensity (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    FiniteMeasure (Icc (0 : ℝ) 1) :=
  FiniteMeasure.map
    (⟨interiorDensityMeasure f 1, section4_full_intensity_finite w f hnorm hf hend⟩ :
      FiniteMeasure ℝ) (projIcc 0 1 zero_le_one)

/-- Projection recovers exactly the real-line density, including its support. -/
theorem fullIntensity_projection_recovery
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    (fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1)).map Subtype.val =
      interiorDensityMeasure f 1 := by
  change ((interiorDensityMeasure f 1).map (projIcc 0 1 zero_le_one)).map
    Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe continuous_projIcc.measurable]
  calc
    _ = (interiorDensityMeasure f 1).map id := by
      apply Measure.map_congr
      filter_upwards [interiorDensityMeasure_ae_mem f 1] with x hx
      have hxx : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      simp only [Function.comp_apply, projIcc_of_mem zero_le_one hxx, id_eq]
    _ = _ := Measure.map_id

/-- Integration against the full intensity is integration of the literal
diagonal density in `eq:intensity-tail-bound`. Endpoints have Lebesgue mass zero. -/
theorem integral_fullIntensity
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    (∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1))) =
      ∫ x in Ioo (0 : ℝ) 1, g (projIcc 0 1 zero_le_one x) * profileDiagonal f x := by
  change (∫ y, g y ∂(interiorDensityMeasure f 1).map (projIcc 0 1 zero_le_one)) = _
  rw [integral_map continuous_projIcc.measurable.aemeasurable
    g.continuous.measurable.aestronglyMeasurable]
  unfold interiorDensityMeasure
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (section4_profileDiagonal_integrable w f hnorm hf hend).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [ENNReal.toReal_ofReal (profileDiagonal_nonneg hf hx.2 ⟨hx.1, le_rfl⟩),
    smul_eq_mul, mul_comm]

/-- The Poisson parameter is exactly the real integral defining λ in the paper. -/
theorem fullIntensity_mass
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    ((fullIntensity w f hnorm hf hend).mass : ℝ) =
      ∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x := by
  have h := integral_fullIntensity w f hnorm hf hend (1 : Icc (0 : ℝ) 1 →ᵇ ℝ)
  simpa only [BoundedContinuousFunction.coe_one, Pi.one_apply, one_mul,
    integral_const, smul_eq_mul, mul_one, Measure.real,
    ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal] using h

/-- Interior continuous-test integrals converge to the full integral, the
intensity-side limiting step in `fixed_points.tex:950–955`. -/
theorem tendsto_integral_interiorIntensity_full_of_tendsto
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {α : ι → ℝ}
    (hα : ∀ i, α i < 1) (hlim : Tendsto α l (𝓝 1))
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    Tendsto (fun i => ∫ y, g y
      ∂(interiorIntensity w f hf (α i) (hα i) : Measure (Icc (0 : ℝ) 1))) l
      (𝓝 (∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1)))) := by
  let μ := interiorDensityMeasure f 1
  let : IsFiniteMeasure μ := section4_full_intensity_finite w f hnorm hf hend
  let gR : ℝ →ᵇ ℝ := g.compContinuous ⟨projIcc 0 1 zero_le_one, continuous_projIcc⟩
  have hi : Integrable gR μ := gR.integrable μ
  have hae : ∀ᵐ x ∂μ, x < 1 := by
    change ∀ᵐ x ∂interiorDensityMeasure f 1, x < 1
    rw [← fullDensityMeasure_restrict_Iio f]
    exact ae_restrict_mem measurableSet_Iio
  have hc := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (f := gR) (F := fun i => (Iic (α i)).indicator gR) (l := l)
    (fun x => ‖gR x‖)
    (Eventually.of_forall fun i => hi.aestronglyMeasurable.indicator measurableSet_Iic)
    (Eventually.of_forall fun i => Eventually.of_forall fun x =>
      norm_indicator_le_norm_self _ _) hi.norm ?_
  · have heq (i : ι) :
        (∫ y, g y ∂(interiorIntensity w f hf (α i) (hα i) : Measure (Icc (0 : ℝ) 1))) =
          ∫ x, (Iic (α i)).indicator gR x ∂μ := by
      rw [integral_indicator measurableSet_Iic]
      change (∫ y, g y ∂(interiorDensityMeasure f (α i)).map (projIcc 0 1 zero_le_one)) = _
      rw [integral_map continuous_projIcc.measurable.aemeasurable
        g.continuous.measurable.aestronglyMeasurable]
      dsimp [μ]
      rw [interiorDensityMeasure_restrict, min_eq_right (hα i).le]
      rfl
    have hfull : (∫ y, g y
        ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1))) = ∫ x, gR x ∂μ :=
      integral_map continuous_projIcc.measurable.aemeasurable
        g.continuous.measurable.aestronglyMeasurable
    simpa only [heq, hfull] using hc
  · filter_upwards [hae] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hlim (Ioi_mem_nhds hx)] with i hi
    exact (indicator_of_mem (s := Iic (α i)) (show x ≤ α i from le_of_lt hi) gR).symm

/-- Real-parameter version for the left limit α ↑ 1. -/
theorem tendsto_integral_interiorIntensity_full
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    Tendsto (fun α : ℝ => if hα : α < 1 then
      ∫ y, g y ∂(interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1))
      else ∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1)))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ y, g y ∂(fullIntensity w f hnorm hf hend : Measure (Icc (0 : ℝ) 1)))) := by
  let a : ℝ → ℝ := fun α => if α < 1 then α else 0
  have ha (α : ℝ) : a α < 1 := by
    dsimp [a]
    split_ifs with h
    · exact h
    · exact zero_lt_one
  have halim : Tendsto a (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    apply (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with α hα
    simp only [mem_Iio] at hα
    simp only [a, if_pos hα, id_eq]
  have h := tendsto_integral_interiorIntensity_full_of_tendsto w f hnorm hf hend ha halim g
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  simp only [mem_Iio] at hα
  simp only [a, if_pos hα, dif_pos hα]

/-- The finite Poisson Laplace functionals converge as the cutoff is removed;
this is the limiting-law half of `fixed_points.tex:950–955`. -/
theorem tendsto_laplace_finitePoissonLaw_interior_full
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ≥0) :
    Tendsto (fun α : ℝ => if hα : α < 1 then
      ∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (interiorIntensity w f hf α hα)
      else ∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (fullIntensity w f hnorm hf hend))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (fullIntensity w f hnorm hf hend))) := by
  let gR : Icc (0 : ℝ) 1 → ℝ := fun x => (g x : ℝ)
  have hg : Measurable gR := (NNReal.continuous_coe.comp g.continuous).measurable
  have hg0 (x : Icc (0 : ℝ) 1) : 0 ≤ gR x := (g x).coe_nonneg
  let q : Icc (0 : ℝ) 1 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => 1 - Real.exp (-gR x), continuous_const.sub
      (Real.continuous_exp.comp (NNReal.continuous_coe.comp g.continuous).neg)⟩
  have h := (Real.continuous_exp.tendsto _).comp
    (tendsto_integral_interiorIntensity_full w f hnorm hf hend q).neg
  rw [integral_pointLaplace_finitePoissonLaw _ gR hg hg0]
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  simp only [mem_Iio] at hα
  simp only [Function.comp_apply, dif_pos hα]
  change Real.exp (-(∫ y, q y
    ∂(interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1)))) =
    ∫ ξ, pointLaplace gR ξ ∂finitePoissonLaw (interiorIntensity w f hf α hα)
  rw [integral_pointLaplace_finitePoissonLaw _ gR hg hg0]
  rfl

end Luce
