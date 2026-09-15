import Luce.Section7Tail

/-! # The common-shape Gamma density envelope mentioned in Section 7 -/

open scoped ENNReal
open MeasureTheory ProbabilityTheory Set Real

namespace Luce.Section7
noncomputable section

theorem gamma_density_integrable {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (gammaPDFReal a r) := by
  have h := integrable_toReal_of_lintegral_ne_top
    (measurable_gammaPDFReal a r).ennreal_ofReal.aemeasurable
    (show (∫⁻ t, ENNReal.ofReal (gammaPDFReal a r t)) ≠ ∞ by
      rw [show (∫⁻ t, ENNReal.ofReal (gammaPDFReal a r t)) = 1 from
        lintegral_gammaPDF_eq_one ha hr]
      exact ENNReal.one_ne_top)
  simpa only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)] using h

def gammaDensity (a r : ℝ) (ha : 0 < a) (hr : 0 < r) : ClockDensity where
  density := gammaPDFReal a r
  measurable := measurable_gammaPDFReal a r
  nonneg := gammaPDFReal_nonneg ha hr
  integrable := gamma_density_integrable ha hr
  integral_one := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (gammaPDFReal_nonneg ha hr))
      (measurable_gammaPDFReal a r).aestronglyMeasurable]
    rw [show (∫⁻ t, ENNReal.ofReal (gammaPDFReal a r t)) = 1 from
      lintegral_gammaPDF_eq_one ha hr]
    simp

theorem gammaDensity_law (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (gammaDensity a r ha hr).law = gammaMeasure a r := rfl

/-- Shape one is the exponential clock law. -/
theorem gammaDensity_one_law (r : ℝ) (hr : 0 < r) :
    (gammaDensity 1 r (by norm_num) hr).law = expMeasure r := rfl

/-- Rate monotonicity of the rate-dependent part of a Gamma density,
after the common cutoff `a/γ`. -/
theorem gamma_rate_envelope {a r γ t : ℝ} (ha : 0 < a) (hγ : 0 < γ)
    (hr : γ ≤ r) (ht : a / γ ≤ t) :
    r ^ a * exp (-(r * t)) ≤ γ ^ a * exp (-(γ * t)) := by
  have hr0 : 0 < r := hγ.trans_le hr
  have hlog := Real.log_le_sub_one_of_pos (div_pos hr0 hγ)
  rw [Real.log_div hr0.ne' hγ.ne'] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog ha.le
  have ht' : a ≤ t * γ := (div_le_iff₀ hγ).mp ht
  have hgap : 0 ≤ r / γ - 1 := by
    rw [sub_nonneg, le_div_iff₀ hγ]
    simpa using hr
  have hlast := mul_le_mul_of_nonneg_right ht' hgap
  have hid : t * γ * (r / γ - 1) = t * (r - γ) := by field_simp
  rw [hid] at hlast
  rw [Real.rpow_def_of_pos hr0, Real.rpow_def_of_pos hγ, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A single integrable envelope for every terminal rate bounded below by
`γ`, at fixed positive Gamma shape. -/
theorem gamma_density_envelope {a r γ t : ℝ} (ha : 0 < a) (hγ : 0 < γ)
    (hr : γ ≤ r) (ht : a / γ ≤ t) :
    gammaPDFReal a r t ≤ gammaPDFReal a γ t := by
  have ht0 : 0 ≤ t := (div_pos ha hγ).le.trans ht
  have h := gamma_rate_envelope ha hγ hr ht
  have hfactor : 0 ≤ t ^ (a - 1) / Real.Gamma a := by positivity
  have hb := mul_le_mul_of_nonneg_right h hfactor
  simp only [gammaPDFReal, if_pos ht0]
  calc
    _ = (r ^ a * exp (-(r * t))) * (t ^ (a - 1) / Real.Gamma a) := by ring
    _ ≤ (γ ^ a * exp (-(γ * t))) * (t ^ (a - 1) / Real.Gamma a) := hb
    _ = _ := by ring

theorem gamma_common_integrable_envelope {a γ : ℝ} (ha : 0 < a) (hγ : 0 < γ) :
    ∃ h : ℝ → ℝ, Integrable h ∧
      ∀ r ≥ γ, ∀ t ≥ a / γ, gammaPDFReal a r t ≤ h t :=
  ⟨gammaPDFReal a γ, gamma_density_integrable ha hγ,
    fun _ hr _ ht => gamma_density_envelope ha hγ hr ht⟩

end
end Luce.Section7
