import Luce.Section4IntensityEstimate

/-! # Finiteness of the full diagonal intensity

Source: `fixed_points.tex:936–952`. Interior density measures are literal
restrictions of one measure, so continuity from below can be applied before
assuming that the full measure has finite mass.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace Luce

/-- Compatibility of the literal interior densities under restriction. -/
theorem interiorDensityMeasure_restrict (f : ℝ → ℝ) (α β : ℝ) :
    (interiorDensityMeasure f α).restrict (Iic β) =
      interiorDensityMeasure f (min α β) := by
  rw [interiorDensityMeasure, restrict_withDensity measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
  tauto

/-- A continuous terminal cutoff, identically one at and beyond b. -/
def terminalIntensityTest (a b : ℝ) : Icc (0 : ℝ) 1 →ᵇ ℝ where
  toFun x := max 0 (min 1 ((x.val - a) / (b - a)))
  continuous_toFun := continuous_const.max (continuous_const.min
    ((continuous_subtype_val.sub continuous_const).div_const _))
  map_bounded' := ⟨1, fun x y => by
    rw [Real.dist_eq, abs_le]
    have hx0 : 0 ≤ max 0 (min 1 ((x.val - a) / (b - a))) := le_max_left _ _
    have hy0 : 0 ≤ max 0 (min 1 ((y.val - a) / (b - a))) := le_max_left _ _
    have hx1 : max 0 (min 1 ((x.val - a) / (b - a))) ≤ (1 : ℝ) :=
      max_le (by norm_num) (min_le_left _ _)
    have hy1 : max 0 (min 1 ((y.val - a) / (b - a))) ≤ (1 : ℝ) :=
      max_le (by norm_num) (min_le_left _ _)
    constructor <;> linarith⟩

lemma terminalIntensityTest_bounds (a b : ℝ) (x : Icc (0 : ℝ) 1) :
    0 ≤ terminalIntensityTest a b x ∧ terminalIntensityTest a b x ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma terminalIntensityTest_zero {a b : ℝ} (hab : a < b)
    (x : Icc (0 : ℝ) 1) (hx : x.val ≤ a) : terminalIntensityTest a b x = 0 := by
  change max 0 (min 1 ((x.val - a) / (b - a))) = 0
  exact max_eq_left ((min_le_right _ _).trans
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le))

lemma terminalIntensityTest_one {a b : ℝ} (hab : a < b)
    (x : Icc (0 : ℝ) 1) (hx : b ≤ x.val) : terminalIntensityTest a b x = 1 := by
  have h : 1 ≤ (x.val - a) / (b - a) := by
    rw [le_div_iff₀ (sub_pos.mpr hab)]
    linarith
  change max 0 (min 1 ((x.val - a) / (b - a))) = 1
  rw [min_eq_left h, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

/-- An upper bound on the continuous terminal test bounds the mass strictly
beyond its upper cutoff. This uses only the already finite interior measure. -/
theorem interiorDensityMeasure_tail_le_test
    (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f)
    {a b β : ℝ} (hab : a < b) (hβ : β < 1) :
    (interiorDensityMeasure f β).real (Ioi b) ≤
      ∫ y, terminalIntensityTest a b y
        ∂(interiorIntensity w f hf β hβ : Measure (Icc (0 : ℝ) 1)) := by
  let μ := interiorDensityMeasure f β
  letI : IsFiniteMeasure μ := interiorDensityMeasure_finite hf hβ
  let g := terminalIntensityTest a b
  have hgm : Measurable (fun x : ℝ => g (projIcc 0 1 zero_le_one x)) :=
    g.continuous.measurable.comp continuous_projIcc.measurable
  have hgi : Integrable (fun x : ℝ => g (projIcc 0 1 zero_le_one x)) μ := by
    apply Integrable.of_bound hgm.aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (terminalIntensityTest_bounds a b _).1]
      exact (terminalIntensityTest_bounds a b _).2
  have heq : (∫ y, g y ∂(interiorIntensity w f hf β hβ : Measure (Icc (0 : ℝ) 1))) =
      ∫ x, g (projIcc 0 1 zero_le_one x) ∂μ := by
    exact integral_map continuous_projIcc.measurable.aemeasurable
      g.continuous.measurable.aestronglyMeasurable
  rw [heq]
  have hi : Integrable ((Ioi b).indicator (fun _ : ℝ => (1 : ℝ))) μ :=
    (integrable_const _).indicator measurableSet_Ioi
  have hle : (Ioi b).indicator (fun _ : ℝ => (1 : ℝ)) ≤ᵐ[μ]
      (fun x => g (projIcc 0 1 zero_le_one x)) := by
    filter_upwards [interiorDensityMeasure_ae_mem f β] with x hx
    by_cases hxb : b < x
    · rw [indicator_of_mem (s := Ioi b) hxb]
      have hxx : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.trans hβ.le⟩
      rw [projIcc_of_mem zero_le_one hxx]
      exact (terminalIntensityTest_one hab ⟨x, hxx⟩ hxb.le).symm.le
    · rw [indicator_of_notMem (s := Ioi b) hxb]
      exact (terminalIntensityTest_bounds a b _).1
  have h := integral_mono_ae hi hgi hle
  simpa only [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_one] using h

lemma interiorDensityMeasure_mono (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    interiorDensityMeasure f a ≤ interiorDensityMeasure f b := by
  rw [← min_eq_right hab, ← interiorDensityMeasure_restrict]
  exact Measure.restrict_le_self

/-- The endpoint estimate prevents the total interior intensity from
diverging as its upper endpoint increases to one. -/
theorem section4_interior_intensity_bounded
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
    ∃ C : ℝ, ∀ β : ℝ, β < 1 → (interiorDensityMeasure f β).real univ ≤ C := by
  obtain ⟨γ, hγ, δ, hδ, htest⟩ := section4_intensity_test_bound w f hnorm hf hend
  let ε := min δ 1 / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by
    have := min_le_left δ 1
    dsimp [ε]
    linarith [lt_min hδ (by norm_num : (0 : ℝ) < 1)]
  let a := 1 - ε
  let b := 1 - ε / 2
  have hab : a < b := by dsimp [a, b]; linarith
  have hb : b < 1 := by dsimp [b]; linarith
  let C := (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4)
  refine ⟨(interiorDensityMeasure f b).real univ + C, ?_⟩
  intro β hβ
  letI : IsFiniteMeasure (interiorDensityMeasure f β) := interiorDensityMeasure_finite hf hβ
  letI : IsFiniteMeasure (interiorDensityMeasure f b) := interiorDensityMeasure_finite hf hb
  have htail : (interiorDensityMeasure f β).real (Ioi b) ≤ C :=
    (interiorDensityMeasure_tail_le_test w f hf hab hβ).trans
      (htest ε hε hεδ β hβ (terminalIntensityTest a b)
        (terminalIntensityTest_bounds a b) (terminalIntensityTest_zero hab))
  have hleft : (interiorDensityMeasure f β).real (Iic b) ≤
      (interiorDensityMeasure f b).real univ := by
    have hμ : (interiorDensityMeasure f β).restrict (Iic b) ≤ interiorDensityMeasure f b := by
      rw [interiorDensityMeasure_restrict]
      exact interiorDensityMeasure_mono f (min_le_right _ _)
    have h := ENNReal.toReal_mono (measure_ne_top (interiorDensityMeasure f b) univ)
      (hμ univ)
    simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.real] using h
  have heq := measureReal_add_measureReal_compl (μ := interiorDensityMeasure f β)
    measurableSet_Iic (s := Iic b)
  rw [compl_Iic] at heq
  linarith

/-- The singleton at one has no density mass, so the increasing open-end
exhaustion captures the entire full intensity. -/
lemma fullDensityMeasure_restrict_Iio (f : ℝ → ℝ) :
    (interiorDensityMeasure f 1).restrict (Iio 1) = interiorDensityMeasure f 1 := by
  rw [interiorDensityMeasure, restrict_withDensity measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  have hs : Iio (1 : ℝ) ∩ Ioc 0 1 = Ioo 0 1 := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨h1, h0, _⟩
      exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h1, h0, h1.le⟩
  rw [hs, Measure.restrict_congr_set Ioo_ae_eq_Ioc]

/-- Equation `eq:intensity-tail-bound`: the full, literal diagonal density
measure is finite under exactly the paper's assumptions. No finiteness or
uniform-integrability premise is carried through from the helper theorems. -/
theorem section4_full_intensity_finite
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
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
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
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
    (hf : ProfileLimit w f) (hend : EndpointAssumption w) :
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

end Luce
