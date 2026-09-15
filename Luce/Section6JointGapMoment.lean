import Luce.Section6GapStartIndependence

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

theorem standardGapLaw_nonneg_ae (n : ℕ) :
    ∀ᵐ ξ ∂standardGapLaw n, ∀ l, 0 ≤ ξ l := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  rw [Filter.eventually_all]
  intro l
  exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => expMeasure 1) unit_exponential_nonneg_ae

/-- The random starting time is retained under the full product spacing law.
No independence or integrability premise is supplied by the caller. -/
theorem joint_gap_moment_bound {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) {a : ℝ} (ha : 0 < a) (p : ℕ) :
    Integrable (fun ξ => exponentialGapMass a (gapStartFromNormalized w σ q ξ)
      (ξ q / orderedRemainingRate w σ q)^p) (standardGapLaw n) ∧
    (∫ ξ, exponentialGapMass a (gapStartFromNormalized w σ q ξ)
      (ξ q / orderedRemainingRate w σ q)^p ∂standardGapLaw n) ≤
      (p.factorial : ℝ)*(a/orderedRemainingRate w σ q)^p*
      (∫ ξ, Real.exp (-((p : ℝ)*a*gapStartFromNormalized w σ q ξ)) ∂standardGapLaw n) := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  let E := fun ξ => Real.exp (-((p : ℝ)*a*gapStartFromNormalized w σ q ξ))
  let Y := fun ξ : Fin n → ℝ => (ξ q)^p
  let X := fun ξ => exponentialGapMass a (gapStartFromNormalized w σ q ξ)
    (ξ q / orderedRemainingRate w σ q)^p
  let C := (a/orderedRemainingRate w σ q)^p
  have hmE : Continuous E := Real.continuous_exp.comp
    (((continuous_gapStartFromNormalized w σ q).const_mul ((p : ℝ)*a)).neg)
  have hmX : Continuous X := by
    dsimp [X]
    unfold gapStartFromNormalized exponentialGapMass survivalKernel
    fun_prop
  have hiY : Integrable Y (standardGapLaw n) :=
    (measurePreserving_eval (fun _ : Fin n => expMeasure 1) q).integrable_comp_of_integrable
      (integrable_pow_expMeasure_one p)
  have hb : ∀ᵐ ξ ∂standardGapLaw n,
      0 ≤ X ξ ∧ X ξ ≤ C*(E ξ*Y ξ) ∧ 0 ≤ Y ξ ∧ 0 ≤ E ξ ∧ E ξ ≤ 1 := by
    filter_upwards [standardGapLaw_nonneg_ae n] with ξ hξ
    have hs := gapStartFromNormalized_nonneg w σ q (fun l _ => hξ l)
    have hh := exponentialGapMass_normalized_pow_le (s := gapStartFromNormalized w σ q ξ)
      ha (orderedRemainingRate_pos w σ q) (hξ q) p
    have he : ((a/orderedRemainingRate w σ q)*survivalKernel (gapStartFromNormalized w σ q ξ) a)^p*
        (ξ q)^p = C*(E ξ*Y ξ) := by
      dsimp [C, E, Y, survivalKernel]
      rw [mul_pow, ← Real.exp_nat_mul]
      rw [show (p : ℝ)*(-gapStartFromNormalized w σ q ξ*a) =
        -((p : ℝ)*a*gapStartFromNormalized w σ q ξ) by ring]
      ring
    refine ⟨hh.1, he ▸ hh.2, pow_nonneg (hξ q) p, (Real.exp_pos _).le, ?_⟩
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (Nat.cast_nonneg p) ha.le) hs)
  have hiEY : Integrable (fun ξ => E ξ*Y ξ) (standardGapLaw n) := by
    apply hiY.mono' (hmE.mul ((continuous_apply q).pow p)).aestronglyMeasurable
    filter_upwards [hb] with ξ h
    change ‖E ξ*Y ξ‖ ≤ Y ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h.2.2.2.1 h.2.2.1)]
    exact mul_le_of_le_one_left h.2.2.1 h.2.2.2.2
  have hiB := hiEY.const_mul C
  have hiX : Integrable X (standardGapLaw n) := by
    apply hiB.mono' hmX.aestronglyMeasurable
    filter_upwards [hb] with ξ h
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2.1
  refine ⟨hiX, ?_⟩
  calc
    _ ≤ ∫ ξ, C*(E ξ*Y ξ) ∂standardGapLaw n := integral_mono_ae hiX hiB (hb.mono fun _ h => h.2.1)
    _ = C*((∫ ξ, E ξ ∂standardGapLaw n)*(p.factorial : ℝ)) := by
      rw [integral_const_mul]
      rw [gapStart_survival_moment_factorization]
    _ = _ := by dsimp [C, E]; ring

end Luce.Section6
