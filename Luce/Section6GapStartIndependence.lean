import Luce.Section6GapStart
import Mathlib.Probability.Independence.Integration

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- The reconstructed start and current normalized spacing are independent
under the actual joint spacing law, for every fixed elimination chain. -/
theorem gapStart_indep_current {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) :
    IndepFun (gapStartFromNormalized w σ q) (fun ξ : Fin n → ℝ => ξ q)
      (standardGapLaw n) := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  have hi := iIndepFun_pi (μ := fun _ : Fin n => expMeasure 1)
    (X := fun l z => z / orderedRemainingRate w σ l)
    (fun l => (measurable_id.div_const _).aemeasurable)
  have hs := hi.indepFun_finsetSum_of_notMem
    (fun l => (measurable_pi_apply l).div_const _) (s := Finset.Iio q) (i := q) (by simp)
  have hc := hs.comp measurable_id (measurable_id.mul_const (orderedRemainingRate w σ q))
  have he : (∑ j ∈ Finset.Iio q, fun ξ : Fin n → ℝ => ξ j / orderedRemainingRate w σ j) =
      gapStartFromNormalized w σ q := by
    ext ξ
    simp [gapStartFromNormalized, Finset.sum_apply]
  simpa [he, standardGapLaw, Function.comp_def,
    ne_of_gt (orderedRemainingRate_pos w σ q)] using hc

/-- The full survival factor separates from the current spacing's moment. -/
theorem gapStart_survival_moment_factorization {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) (a : ℝ) (p : ℕ) :
    (∫ ξ, Real.exp (-((p : ℝ)*a*gapStartFromNormalized w σ q ξ))*(ξ q)^p
      ∂standardGapLaw n) =
      (∫ ξ, Real.exp (-((p : ℝ)*a*gapStartFromNormalized w σ q ξ))
        ∂standardGapLaw n)*(p.factorial : ℝ) := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  have hi := (gapStart_indep_current w σ q).comp
    (show Measurable (fun s : ℝ => Real.exp (-((p : ℝ)*a*s))) by fun_prop)
    (show Measurable (fun z : ℝ => z^p) by fun_prop)
  have hm : Continuous (fun ξ => Real.exp (-((p : ℝ)*a*gapStartFromNormalized w σ q ξ))) := by
    exact Real.continuous_exp.comp
      (((continuous_gapStartFromNormalized w σ q).const_mul ((p : ℝ)*a)).neg)
  have he : (∫ ξ : Fin n → ℝ, (ξ q)^p ∂standardGapLaw n) = (p.factorial : ℝ) := by
    have hh := integral_map (μ := Measure.pi (fun _ : Fin n => expMeasure 1))
      (measurable_pi_apply q).aemeasurable (f := fun z : ℝ => z^p)
      (continuous_id.pow p).aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin n => expMeasure 1) q).map_eq] at hh
    exact hh.symm.trans (integral_pow_expMeasure_one p)
  calc
    _ = (∫ ξ, Real.exp (-((p : ℝ)*a*gapStartFromNormalized w σ q ξ)) ∂standardGapLaw n)*
        (∫ ξ : Fin n → ℝ, (ξ q)^p ∂standardGapLaw n) :=
      hi.integral_mul_eq_mul_integral hm.aestronglyMeasurable
        ((continuous_apply q).pow p).aestronglyMeasurable
    _ = _ := by rw [he]

end Luce.Section6
