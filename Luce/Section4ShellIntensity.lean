import Luce.Section4ShellIntensityBound

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace Luce.Shell

theorem section4_full_intensity_finite
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
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
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
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
    (hf : ProfileLimit w f) (hend : EndpointShellAssumption w) :
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

end Luce.Shell
