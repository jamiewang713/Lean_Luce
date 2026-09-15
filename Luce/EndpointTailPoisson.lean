import Luce.EndpointExpectationTightness
import Luce.Section4ShellTheorem

/-! The finite-mean Poisson completion from endpoint expectation tightness.
The proof follows the existing Section 4 intensity and approximation argument;
all endpoint information enters through the proved expectation property.
This reusable theorem is specialized to the raw Corollary 4.7 condition in
`Luce.EndpointExceptionalTheorem`. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.EndpointTail

theorem intensity_test_bound (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w) :
    ∀ η : ℝ, 0 < η → ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      ∀ β : ℝ, ∀ hβ : β < 1, ∀ g : Icc (0 : ℝ) 1 →ᵇ ℝ,
        (∀ x, 0 ≤ g x ∧ g x ≤ 1) → (∀ x, x.val ≤ a → g x = 0) →
        (∫ y, g y ∂(interiorIntensity w f hf β hβ : Measure (Icc (0 : ℝ) 1))) ≤ η := by
  intro η hη
  obtain ⟨a, ha0, ha1, hest⟩ := hend η hη
  refine ⟨a, ha0, ha1, ?_⟩
  intro β hβ g hg hs
  let A := fun n => ∫ e, ∫ y, g y
    ∂((interiorFixedPoints β (raceDraw e)).toFiniteMeasure : Measure (Icc (0 : ℝ) 1))
    ∂exponentialRace (w n)
  have hupper : ∀ᶠ n : ℕ in atTop, A n ≤ η := hest.mono fun n hn =>
    (integral_interior_observed_test_le_tail (w n) a β g hg hs).trans hn.le
  have hbounded : IsBoundedUnder (· ≤ ·) atTop A := ⟨η, hupper⟩
  apply (section4_interior_test_expectation_lower w f hnorm hf hβ g
    (fun x => (hg x).1) hbounded).trans
  exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n =>
    integral_nonneg (fun e => integral_nonneg (fun y => (hg y).1)))) hupper

theorem section4_interior_intensity_bounded
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w) :
    ∃ C : ℝ, ∀ β : ℝ, β < 1 → (interiorDensityMeasure f β).real univ ≤ C := by
  obtain ⟨a, _, ha, htest⟩ := intensity_test_bound w f hnorm hf hend 1 zero_lt_one
  let b := (a+1)/2
  have hab : a < b := by dsimp [b]; linarith
  have hb : b < 1 := by dsimp [b]; linarith
  refine ⟨(interiorDensityMeasure f b).real univ + 1, ?_⟩
  intro β hβ
  letI : IsFiniteMeasure (interiorDensityMeasure f β) := interiorDensityMeasure_finite hf hβ
  letI : IsFiniteMeasure (interiorDensityMeasure f b) := interiorDensityMeasure_finite hf hb
  have htail : (interiorDensityMeasure f β).real (Ioi b) ≤ 1 :=
    (interiorDensityMeasure_tail_le_test w f hf hab hβ).trans
      (htest β hβ (terminalIntensityTest a b)
        (terminalIntensityTest_bounds a b) (terminalIntensityTest_zero hab))
  have hleft : (interiorDensityMeasure f β).real (Iic b) ≤
      (interiorDensityMeasure f b).real univ := by
    have hμ : (interiorDensityMeasure f β).restrict (Iic b) ≤ interiorDensityMeasure f b := by
      rw [interiorDensityMeasure_restrict]
      exact interiorDensityMeasure_mono f (min_le_right _ _)
    have h := ENNReal.toReal_mono (measure_ne_top (interiorDensityMeasure f b) univ) (hμ univ)
    simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.real] using h
  have heq := measureReal_add_measureReal_compl (μ := interiorDensityMeasure f β)
    measurableSet_Iic (s := Iic b)
  rw [compl_Iic] at heq
  linarith

end Luce.EndpointTail
end

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.EndpointTail

theorem section4_full_intensity_finite
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w) :
    IsFiniteMeasure (interiorDensityMeasure f 1) := by
  obtain ⟨C, hC⟩ := section4_interior_intensity_bounded w f hnorm hf hend
  let β : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  have hβ (n : ℕ) : β n < 1 := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    dsimp [β]
    linarith
  have hlim : Tendsto β atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmono : Monotone β := by
    intro i j hij
    dsimp [β]
    gcongr
  have hcover := iUnion_Iic_eq_Iio_of_lt_of_tendsto hβ hlim
  let μ := interiorDensityMeasure f 1
  have hbound (n : ℕ) : μ (Iic (β n)) ≤ ENNReal.ofReal C := by
    letI : IsFiniteMeasure (interiorDensityMeasure f (β n)) :=
      interiorDensityMeasure_finite hf (hβ n)
    have heq : μ (Iic (β n)) = interiorDensityMeasure f (β n) univ := by
      have h := congrArg (fun ν : Measure ℝ => ν univ) (interiorDensityMeasure_restrict f 1 (β n))
      simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter,
        min_eq_right (hβ n).le] using h
    rw [heq, ← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hC (β n) (hβ n))
  have hmass : μ univ = μ (Iio 1) := by
    have h := congrArg (fun ν : Measure ℝ => ν univ) (fullDensityMeasure_restrict_Iio f)
    simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using h.symm
  have hsets : Monotone (fun n => Iic (β n)) :=
    fun _ _ hij => Iic_subset_Iic.mpr (hmono hij)
  refine ⟨?_⟩
  change μ univ < ⊤
  rw [hmass, ← hcover, hsets.directed_le.measure_iUnion]
  exact (iSup_le hbound).trans_lt ENNReal.ofReal_lt_top

/-- The diagonal is measurably defined over the full open interval by its
already proved local integrability. No endpoint value is prescribed. -/
lemma aestronglyMeasurable_profileDiagonal_full
    {w : WeightArray} {f : ℝ → ℝ} (hf : ProfileLimit w f) :
    AEStronglyMeasurable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  let β : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  have hβ (n : ℕ) : β n < 1 := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    dsimp [β]
    linarith
  have hlim : Tendsto β atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hc := iUnion_Iic_eq_Iio_of_lt_of_tendsto hβ hlim
  have hcover : (⋃ n, Ioc (0 : ℝ) (β n)) = Ioo 0 1 := by
    have h := congrArg (fun s : Set ℝ => Ioi 0 ∩ s) hc
    simpa only [inter_iUnion, Ioi_inter_Iic, Ioi_inter_Iio] using h
  rw [← hcover, aestronglyMeasurable_iUnion_iff]
  exact fun n => (integrable_profileDiagonal hf (hβ n)).aestronglyMeasurable

/-- The full real Lebesgue integral in the definition of λ is a genuine
integral of an integrable function, rather than a totalized divergent integral. -/
theorem section4_profileDiagonal_integrable
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hm := aestronglyMeasurable_profileDiagonal_full hf
  have hpos : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] profileDiagonal f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact profileDiagonal_nonneg hf hx.2 ⟨hx.1, le_rfl⟩
  apply (lintegral_ofReal_ne_top_iff_integrable hm hpos).mp
  haveI := section4_full_intensity_finite w f hnorm hf hend
  have h := measure_ne_top (interiorDensityMeasure f 1) univ
  rw [interiorDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h
  exact h

/-- The second assertion of `eq:intensity-tail-bound`, with Lebesgue endpoint
conventions made explicit. Integrability has already been proved above. -/
theorem section4_intensity_tail_tendsto
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w) :
    Tendsto (fun α : ℝ => ∫ x in Ioo α 1, profileDiagonal f x)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hi := section4_profileDiagonal_integrable w f hnorm hf hend
  let F := fun α : ℝ => (Ioi α).indicator (profileDiagonal f)
  have hlim : Tendsto (fun α => ∫ x in Ioo (0 : ℝ) 1, F α x)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioo (0 : ℝ) 1)) (f := fun _ => (0 : ℝ))
      (F := F) (l := 𝓝[<] (1 : ℝ))
      (fun x => ‖profileDiagonal f x‖)
      (Eventually.of_forall fun α => hi.aestronglyMeasurable.indicator measurableSet_Ioi)
      (Eventually.of_forall fun α => Eventually.of_forall fun x =>
        norm_indicator_le_norm_self _ _) hi.norm ?_
    · simpa only [integral_zero] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [show ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), x < α from
        nhdsWithin_le_nhds (Ioi_mem_nhds hx.2)] with α hα
      exact (indicator_of_notMem (s := Ioi α) (not_lt.mpr hα.le) _).symm
  apply hlim.congr'
  filter_upwards [show ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), 0 < α from
    nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)] with α hα
  dsimp [F]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨hax, _, hx1⟩
    exact ⟨hax, hx1⟩
  · rintro ⟨hax, hx1⟩
    exact ⟨hax, hα.trans hax, hx1⟩

end Luce.EndpointTail
end

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace Luce.EndpointTail

/-- The manuscript's full diagonal intensity as a finite measure on [0,1]. -/
def fullIntensity (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w) :
    FiniteMeasure (Icc (0 : ℝ) 1) :=
  FiniteMeasure.map
    (⟨interiorDensityMeasure f 1, section4_full_intensity_finite w f hnorm hf hend⟩ :
      FiniteMeasure ℝ) (projIcc 0 1 zero_le_one)

/-- Projection recovers exactly the real-line density, including its support. -/
theorem fullIntensity_projection_recovery
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w) :
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
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w)
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
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w) :
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
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w)
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
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w)
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
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w)
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

end Luce.EndpointTail
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

namespace Luce.EndpointTail

/-- The full process has the Poisson Laplace limit, under exactly the
normalized model and the paper's profile and endpoint assumptions. -/
theorem section4_full_laplace
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ≥0) :
    Tendsto (fun n => ∫ e, pointLaplace (fun x => (g x : ℝ))
      (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
        ∂finitePoissonLaw (fullIntensity w f hnorm hf hend))) := by
  let v := fun α n => ∫ e, pointLaplace (fun x => (g x : ℝ))
    (interiorFixedPoints α (raceDraw e)) ∂exponentialRace (w n)
  let a := fun α : ℝ => if hα : α < 1 then
    ∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
      ∂finitePoissonLaw (interiorIntensity w f hf α hα)
    else ∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ
      ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)
  let p := fun α n => (exponentialRace (w n)).real {e | 0 < tailFixedPointCount e α}
  have hp (α : ℝ) : IsBoundedUnder (· ≤ ·) atTop (p α) :=
    ⟨1, show ∀ᶠ n : ℕ in atTop, p α n ≤ 1 from
      Eventually.of_forall fun _ => measureReal_le_one⟩
  have htail : Tendsto (fun α => limsup (p α) atTop) (𝓝[<] (1 : ℝ)) (𝓝 0) :=
    hend.probability_tightness
  apply tendsto_of_terminal_approximation _ v a p _ hp htail
    (tendsto_laplace_finitePoissonLaw_interior_full w f hnorm hf hend g)
  · intro α hα
    have h := pointMeasure_laplace_of_integrals (fun n => exponentialRace (w n))
      (fun n => raceInteriorBernoulli (w n) α) section3Location
      (interiorIntensity w f hf α hα)
      (section3_predictable_tests w f hnorm hf hα)
      (section3_predictable_maximum w f hnorm hf hα) g
    simpa only [raceInteriorBernoulli_pointMeasure, a, dif_pos hα] using h
  · intro α _ n
    exact section4_laplace_cutoff_error (w n) α g

/-- Equation `eq:point-process-limit`: convergence of the actual full
finite point measure in its weak topology. Every bounded continuous test
of the point measure is allowed, and all approximation and tightness
conditions have been proved from the model assumptions. -/
theorem section4_full_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w)
    (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend))) := by
  let μ : ℕ → Measure (FinitePointMeasure (Icc (0 : ℝ) 1)) :=
    fun n => (exponentialRace (w n)).map (fun e => fixedPoints (raceDraw e))
  let Q := finitePoissonLaw (fullIntensity w f hnorm hf hend)
  have hΞ (n : ℕ) : Measurable (fun e : Fin n → ℝ => fixedPoints (raceDraw e)) :=
    measurable_interiorFixedPoints_race (w n) 1
  haveI (n : ℕ) : IsProbabilityMeasure (μ n) :=
    Measure.isProbabilityMeasure_map (hΞ n).aemeasurable
  have hLaplace (g : Icc (0 : ℝ) 1 →ᵇ ℝ≥0) :
      Tendsto (fun n => ∫ ξ, momentLaplace g (pointMoment ξ) ∂μ n) atTop
        (𝓝 (∫ ξ, momentLaplace g (pointMoment ξ) ∂Q)) := by
    simp_rw [momentLaplace_pointMoment_eq_pointLaplace]
    have hg := (NNReal.continuous_coe.comp g.continuous).measurable
    have heq (n : ℕ) : (∫ ξ, pointLaplace (fun x => (g x : ℝ)) ξ ∂μ n) =
        ∫ e, pointLaplace (fun x => (g x : ℝ)) (fixedPoints (raceDraw e))
          ∂exponentialRace (w n) :=
      integral_map_of_stronglyMeasurable (hΞ n)
        (measurable_pointLaplace _ hg (fun x => (g x).coe_nonneg)).stronglyMeasurable
    simp_rw [heq]
    exact section4_full_laplace w f hnorm hf hend g
  have h := pointMeasure_law_convergence_of_laplace μ Q hLaplace
    (pointMeasure_tightness_of_laplace μ Q hLaplace) F
  have heq (n : ℕ) : (∫ ξ, F ξ ∂μ n) =
      ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n) :=
    integral_map_of_stronglyMeasurable (hΞ n)
      (measurable_boundedContinuous_pointMeasure F).stronglyMeasurable
  simpa only [heq] using h

/-- The full point-process limit for every Luce permutation realization.
The row masses are precisely `eq:luce-law`; no coupling between rows or
asymptotic hypothesis beyond the manuscript assumptions is required. -/
theorem section4_full_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ)
    (F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
      (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend))) := by
  have heq (n : ℕ) : (∫ ω, F (fixedPoints (π n ω)) ∂P n) =
      ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n) := by
    letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
    have htest : Measurable (fun σ : Equiv.Perm (Fin n) => F (fixedPoints σ)) :=
      fun _ _ => trivial
    calc
      _ = ∫ σ, F (fixedPoints σ) ∂(P n).map (π n) :=
        (integral_map_of_stronglyMeasurable (hπ n) htest.stronglyMeasurable).symm
      _ = ∫ σ, F (fixedPoints σ) ∂(exponentialRace (w n)).map raceDraw := by
        rw [luce_map_eq_raceDraw (P n) (w n) (π n) (hπ n) (hMass n)]
      _ = _ := integral_map_of_stronglyMeasurable (measurable_raceDraw n) htest.stronglyMeasurable
  simpa only [heq] using section4_full_poisson w f hnorm hf hend F

end Luce.EndpointTail
end

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.EndpointTail

theorem fullIntensity_mass_eq_toNNReal_integral
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w) :
    (fullIntensity w f hnorm hf hend).mass =
      Real.toNNReal (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x) := by
  rw [← fullIntensity_mass w f hnorm hf hend]
  simp

/-- Equation `eq:count-poisson`: the full count law converges in probability
total variation to Poisson with the literal diagonal integral as parameter. -/
theorem section4_count_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w) :
    Tendsto (fun n => probabilityTotalVariation (raceFixedPointCountLaw (w n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0) := by
  have h := fixedPointCountLaw_totalVariation_of_pointProcess (fun n => Fin n → ℝ)
    (fun n => exponentialRace (w n)) (fun _ => raceDraw) (fun n => measurable_raceDraw n)
    (fullIntensity w f hnorm hf hend) (section4_full_poisson w f hnorm hf hend)
  rw [fullIntensity_mass_eq_toNNReal_integral w f hnorm hf hend] at h
  exact h

/-- The total-variation conclusion for arbitrary realizations of the Luce
law, with only its defining finite masses and the manuscript assumptions. -/
theorem section4_count_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) :
    Tendsto (fun n => probabilityTotalVariation
      (fixedPointCountLaw (P n) (π n) (hπ n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0) := by
  have h := fixedPointCountLaw_totalVariation_of_pointProcess Ω P π hπ
    (fullIntensity w f hnorm hf hend)
    (section4_full_poisson_general Ω P w f hnorm hf hend π hπ hMass)
  rw [fullIntensity_mass_eq_toNNReal_integral w f hnorm hf hend] at h
  exact h

end Luce.EndpointTail
end

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.EndpointTail

theorem section4_main_poisson
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    (∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
      Tendsto (fun n => ∫ e, F (fixedPoints (raceDraw e)) ∂exponentialRace (w n)) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))) ∧
    Tendsto (fun n => probabilityTotalVariation (raceFixedPointCountLaw (w n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0) :=
  ⟨section4_profileDiagonal_integrable w f hnorm hf hend,
    section4_full_poisson w f hnorm hf hend,
    section4_count_poisson w f hnorm hf hend⟩

/-- The same complete theorem for arbitrary row probability spaces and
measurable Luce permutations with the manuscript's exact finite masses.
Cross-row independence, regularity of the profile beyond L¹ convergence,
and global upper/lower rate bounds are not hypotheses. -/
theorem section4_main_poisson_general
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointExpectationTightness w)
    (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ) :
    Integrable (profileDiagonal f) (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    (∀ F : FinitePointMeasure (Icc (0 : ℝ) 1) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, F (fixedPoints (π n ω)) ∂P n) atTop
        (𝓝 (∫ ξ, F ξ ∂finitePoissonLaw (fullIntensity w f hnorm hf hend)))) ∧
    Tendsto (fun n => probabilityTotalVariation (fixedPointCountLaw (P n) (π n) (hπ n))
      (poissonProbabilityMeasure (Real.toNNReal
        (∫ x in Ioo (0 : ℝ) 1, profileDiagonal f x)))) atTop (𝓝 0) :=
  ⟨section4_profileDiagonal_integrable w f hnorm hf hend,
    section4_full_poisson_general Ω P w f hnorm hf hend π hπ hMass,
    section4_count_poisson_general Ω P w f hnorm hf hend π hπ hMass⟩

end Luce.EndpointTail
end

