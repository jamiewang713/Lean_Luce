import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities

noncomputable section
open MeasureTheory Set
namespace Luce.Section6

/-- Cauchy--Schwarz on an arbitrary measurable event. The event can
depend on every coordinate of the random variable. -/
theorem setIntegral_le_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {F : Ω → ℝ} {A : Set Ω}
    (hF : Integrable F μ) (hF2 : Integrable (fun z => F z^2) μ)
    (hF0 : ∀ᵐ z ∂μ, 0 ≤ F z) :
    (∫ z in A, F z ∂μ) ≤
      Real.sqrt (∫ z, F z^2 ∂μ)*Real.sqrt (μ.real A) := by
  have hmem : MemLp F (ENNReal.ofReal (2 : ℝ)) (μ.restrict A) := by
    norm_num only [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hF.integrableOn.aestronglyMeasurable).mpr hF2.integrableOn
  have hconst : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) (μ.restrict A) := memLp_const 1
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := 2) (q := 2) (by constructor <;> norm_num)
    (ae_restrict_of_ae hF0) (Filter.Eventually.of_forall (fun _ => zero_le_one)) hmem hconst
  simp only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
    Measure.real, Measure.restrict_apply_univ] at hholder
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  apply hholder.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt (setIntegral_le_integral hF2
    (Filter.Eventually.of_forall (fun z => sq_nonneg (F z))))

/-- Split an expectation comparison into a good-event error and the
two actual bad-event products. This uses no independence of the event. -/
theorem integral_comparison_good_bad {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F Y E : Ω → ℝ} {G : Set Ω} (hG : MeasurableSet G)
    (hF : Integrable F μ) (hY : Integrable Y μ) (hE : Integrable E μ)
    (hF0 : ∀ᵐ z ∂μ, 0 ≤ F z) (hY0 : ∀ᵐ z ∂μ, 0 ≤ Y z)
    (hE0 : ∀ᵐ z ∂μ, 0 ≤ E z)
    (herr : ∀ᵐ z ∂μ, z ∈ G → |F z-Y z| ≤ E z) :
    |(∫ z, F z ∂μ)-(∫ z, Y z ∂μ)| ≤
      (∫ z, E z ∂μ)+(∫ z in Gᶜ, F z ∂μ)+(∫ z in Gᶜ, Y z ∂μ) := by
  have hdiff := hF.sub hY
  have hgood : (∫ z in G, |F z-Y z| ∂μ) ≤ ∫ z, E z ∂μ := by
    apply le_trans (integral_mono_ae hdiff.abs.integrableOn hE.integrableOn ?_)
      (setIntegral_le_integral hE hE0)
    exact (ae_restrict_iff' hG).mpr herr
  have hbad : (∫ z in Gᶜ, |F z-Y z| ∂μ) ≤
      (∫ z in Gᶜ, F z ∂μ)+(∫ z in Gᶜ, Y z ∂μ) := by
    rw [← integral_add hF.integrableOn hY.integrableOn]
    apply integral_mono_ae hdiff.abs.integrableOn (hF.add hY).integrableOn
    filter_upwards [ae_restrict_of_ae hF0, ae_restrict_of_ae hY0] with z hf hy
    exact (abs_sub_le (F z) 0 (Y z)).trans_eq (by simp [abs_of_nonneg hf, abs_of_nonneg hy])
  calc
    _ = |∫ z, F z-Y z ∂μ| := by rw [integral_sub hF hY]
    _ ≤ ∫ z, |F z-Y z| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => F z-Y z)
    _ = (∫ z in G, |F z-Y z| ∂μ)+(∫ z in Gᶜ, |F z-Y z| ∂μ) :=
      (integral_add_compl hG hdiff.abs).symm
    _ ≤ _ := by linarith only [hgood, hbad]

end Luce.Section6
