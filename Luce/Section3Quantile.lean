import Luce.ProfileRegularity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The deterministic inverse in the interior race law

These lemmas prove the analytic prerequisites used in `fixed_points.tex`
lines 242–243 and 728–732.  The profile measure is abstract in the auxiliary
statements; its probability normalization and almost-everywhere positivity
will be discharged from the manuscript's profile assumption.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Luce

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private lemma integral_pos_of_ae_pos [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : Integrable g μ) (hpos : ∀ᵐ x ∂μ, 0 < g x) :
    0 < ∫ x, g x ∂μ := by
  have hnonneg : 0 ≤ᵐ[μ] g := hpos.mono fun _ h => h.le
  have hne : (∫ x, g x ∂μ) ≠ 0 := by
    intro hz
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hg).mp hz
    obtain ⟨x, hx, hzx⟩ := (hpos.and hzero).exists
    simp only [Pi.zero_apply] at hzx
    linarith
  exact lt_of_le_of_ne (integral_nonneg_of_ae hnonneg) hne.symm

/-- Strict positivity of the limiting remaining rate at every finite
nonnegative time; this supplies the interior denominator bound. -/
theorem profileD_pos [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {t : ℝ} (ht : 0 ≤ t) :
    0 < profileD μ f t := by
  apply integral_pos_of_ae_pos (integrable_rateKernel hf (hpos.mono fun _ h => h.le) ht)
  filter_upwards [hpos] with x hx
  exact mul_pos hx (survivalKernel_pos _ _)

/-- The lower endpoint of the distribution transform is exactly zero. -/
@[simp] theorem profileF_zero [IsProbabilityMeasure μ] (f : Ω → ℝ) :
    profileF μ f 0 = 0 := by
  simp [profileF, profileH, survivalKernel]

/-- The distribution transform is strictly increasing, as asserted before
the definition of the inverse time `t_x` in the manuscript. -/
theorem strictMonoOn_profileF [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    StrictMonoOn (profileF μ f) (Ici 0) := by
  intro s hs t ht hst
  have hf0 := hpos.mono fun _ h => h.le
  have his := integrable_survivalKernel hf.aestronglyMeasurable hf0 hs
  have hit := integrable_survivalKernel hf.aestronglyMeasurable hf0 ht
  have hdiff : 0 < ∫ x, survivalKernel s (f x) - survivalKernel t (f x) ∂μ := by
    apply integral_pos_of_ae_pos (his.sub hit)
    filter_upwards [hpos] with x hx
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    nlinarith
  rw [integral_sub his hit] at hdiff
  dsimp [profileF, profileH]
  linarith

/-- At every finite time the distribution transform remains below one. -/
theorem profileF_lt_one [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {t : ℝ} (ht : 0 ≤ t) :
    profileF μ f t < 1 := by
  have hH : 0 < profileH μ f t :=
    integral_pos_of_ae_pos
      (integrable_survivalKernel hf.aestronglyMeasurable (hpos.mono fun _ h => h.le) ht)
      (Eventually.of_forall fun x => survivalKernel_pos t (f x))
  dsimp [profileF]
  linarith

theorem profileF_nonneg [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ profileF μ f t := by
  have h := (strictMonoOn_profileF hf hpos).monotoneOn
    (show (0 : ℝ) ∈ Ici 0 from by simp) ht ht
  simpa only [profileF_zero] using h

/-- Dominated convergence identifies the upper endpoint of the limiting
distribution transform, using positivity rather than a lower bound on `f`. -/
theorem tendsto_profileF_atTop [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    Tendsto (profileF μ f) atTop (𝓝 1) := by
  have hf0 := hpos.mono fun _ h => h.le
  have hH : Tendsto (profileH μ f) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (F := fun t x => survivalKernel t (f x)) (f := fun _ => (0 : ℝ))
      (fun _ => (1 : ℝ))
      (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
          exact (integrable_survivalKernel hf.aestronglyMeasurable hf0 ht).aestronglyMeasurable)
      (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
          filter_upwards [hf0] with x hx
          simpa [Real.norm_eq_abs, abs_of_pos (survivalKernel_pos t (f x))] using
            survivalKernel_le_one ht hx)
      (integrable_const 1)
      (by filter_upwards [hpos] with x hx
          have ht : Tendsto (fun t : ℝ => t * f x) atTop atTop :=
            (tendsto_mul_const_atTop_of_pos hx).mpr tendsto_id
          simpa only [Function.comp_def, survivalKernel, neg_mul] using
            Real.tendsto_exp_neg_atTop_nhds_zero.comp ht)
    change Tendsto (fun t => ∫ x, survivalKernel t (f x) ∂μ) atTop (𝓝 0)
    simpa only [integral_zero] using h
  change Tendsto (fun t => 1 - profileH μ f t) atTop (𝓝 1)
  simpa only [sub_zero] using hH.const_sub 1

/-- Every interior spatial coordinate, including zero, has a nonnegative
inverse time. This establishes existence before defining or using the inverse. -/
theorem exists_profileF_eq [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {x : ℝ}
    (hx : x ∈ Ico 0 1) : ∃ t ∈ Ici (0 : ℝ), profileF μ f t = x := by
  obtain ⟨T, hT0, hTx⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    ((tendsto_profileF_atTop hf hpos).eventually (lt_mem_nhds hx.2))).exists
  have hc : ContinuousOn (profileF μ f) (Icc 0 T) :=
    (continuousOn_profileF hf.aestronglyMeasurable (hpos.mono fun _ h => h.le)).mono
      (fun _ ht => ht.1)
  obtain ⟨t, ht, htx⟩ := intermediate_value_Icc hT0 hc
    (show x ∈ Icc (profileF μ f 0) (profileF μ f T) from
      ⟨by simpa only [profileF_zero] using hx.1, hTx.le⟩)
  exact ⟨t, ht.1, htx⟩

/-- The inverse used for the paper's `t_x`: standard `invFunOn` restricts
the time variable to the nonnegative half-line. Its values outside the
distribution's image are irrelevant; no inverse property is built in. -/
def profileQuantile (μ : Measure Ω) (f : Ω → ℝ) (x : ℝ) : ℝ :=
  Function.invFunOn (profileF μ f) (Ici 0) x

theorem profileQuantile_nonneg [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {x : ℝ}
    (hx : x ∈ Ico 0 1) : 0 ≤ profileQuantile μ f x :=
  Function.invFunOn_mem (exists_profileF_eq hf hpos hx)

/-- The inverse is an actual right inverse on the full interval `[0,1)`. -/
theorem profileF_profileQuantile [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {x : ℝ}
    (hx : x ∈ Ico 0 1) : profileF μ f (profileQuantile μ f x) = x :=
  Function.invFunOn_eq (exists_profileF_eq hf hpos hx)

/-- Strict increase also proves uniqueness of every nonnegative inverse time. -/
theorem profileQuantile_profileF [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {t : ℝ} (ht : 0 ≤ t) :
    profileQuantile μ f (profileF μ f t) = t :=
  (strictMonoOn_profileF hf hpos).injOn.leftInvOn_invFunOn ht

/-- The inverse endpoint convention required in Section 3 is forced by `F 0 = 0`. -/
theorem profileQuantile_zero [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    profileQuantile μ f 0 = 0 := by
  simpa only [profileF_zero] using profileQuantile_profileF hf hpos (le_refl (0 : ℝ))

theorem strictMonoOn_profileQuantile [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    StrictMonoOn (profileQuantile μ f) (Ico 0 1) := by
  intro x hx y hy hxy
  by_contra hn
  have hle := (strictMonoOn_profileF hf hpos).monotoneOn
    (profileQuantile_nonneg hf hpos hy) (profileQuantile_nonneg hf hpos hx)
    (le_of_not_gt hn)
  rw [profileF_profileQuantile hf hpos hy, profileF_profileQuantile hf hpos hx] at hle
  exact (not_le_of_gt hxy) hle

/-- The inverse is continuous on `[0,1)`, including at zero. No regularity
of the original profile beyond integrability and positivity is imposed. -/
theorem continuousOn_profileQuantile [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    ContinuousOn (profileQuantile μ f) (Ico 0 1) := by
  let q : Ico (0 : ℝ) 1 → Ici (0 : ℝ) := fun x =>
    ⟨profileQuantile μ f x, profileQuantile_nonneg hf hpos x.property⟩
  have hqmono : Monotone q := by
    intro x y hxy
    exact (strictMonoOn_profileQuantile hf hpos).monotoneOn x.property y.property hxy
  have hqsurj : Function.Surjective q := by
    intro t
    have hFt0 : 0 ≤ profileF μ f t := by
      have h := (strictMonoOn_profileF hf hpos).monotoneOn
        (show (0 : ℝ) ∈ Ici 0 from by simp) t.property t.property
      simpa only [profileF_zero] using h
    refine ⟨⟨profileF μ f t, hFt0, profileF_lt_one hf hpos t.property⟩, ?_⟩
    apply Subtype.ext
    exact profileQuantile_profileF hf hpos t.property
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_subtype_val.comp (hqmono.continuous_of_surjective hqsurj))

/-- A uniform inversion modulus on an interior spatial interval. The time
cutoff has a strict CDF margin beyond `α`, so an empirical CDF error smaller
than `δ` also confines all the relevant order statistics to this time cutoff.
This is the quantitative step behind `eq:uniform-quantile`. -/
theorem uniform_profile_inverse_modulus [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) {α ε : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ T δ : ℝ, 0 ≤ T ∧ 0 < δ ∧ α + δ < profileF μ f T ∧
      ∀ x ∈ Icc (0 : ℝ) α, ∀ t ∈ Icc (0 : ℝ) T,
        |profileF μ f t - x| < δ → |t - profileQuantile μ f x| < ε := by
  let β : ℝ := (α + 1) / 2
  have hαβ : α < β := by dsimp [β]; linarith
  have hβ0 : 0 ≤ β := hα0.trans hαβ.le
  have hβ1 : β < 1 := by dsimp [β]; linarith
  have hβ : β ∈ Ico (0 : ℝ) 1 := ⟨hβ0, hβ1⟩
  have hc : ContinuousOn (profileQuantile μ f) (Icc 0 β) :=
    (continuousOn_profileQuantile hf hpos).mono fun _ hx => ⟨hx.1, hx.2.trans_lt hβ1⟩
  obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) ε hε
  let T : ℝ := profileQuantile μ f β
  let δ : ℝ := min (r / 2) ((β - α) / 2)
  have hδ : 0 < δ := lt_min (half_pos hr) (half_pos (sub_pos.mpr hαβ))
  have hT : 0 ≤ T := profileQuantile_nonneg hf hpos hβ
  have hFT : profileF μ f T = β := profileF_profileQuantile hf hpos hβ
  refine ⟨T, δ, hT, hδ, ?_, ?_⟩
  · rw [hFT]
    have : δ ≤ (β - α) / 2 := min_le_right _ _
    linarith
  · intro x hx t ht herr
    have hFt : profileF μ f t ∈ Icc (0 : ℝ) β := by
      refine ⟨profileF_nonneg hf hpos ht.1, ?_⟩
      rw [← hFT]
      exact (strictMonoOn_profileF hf hpos).monotoneOn ht.1 hT ht.2
    have hxr : x ∈ Icc (0 : ℝ) β := ⟨hx.1, hx.2.trans hαβ.le⟩
    have hdist : dist (profileF μ f t) x < r := by
      rw [Real.dist_eq]
      have : δ ≤ r / 2 := min_le_left _ _
      linarith
    have h := hmod (profileF μ f t) hFt x hxr hdist
    rw [Real.dist_eq, profileQuantile_profileF hf hpos ht.1] at h
    exact h

end Luce
