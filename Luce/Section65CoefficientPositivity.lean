import Luce.Section6TraceDensity
import Luce.Section6Sampling
import Luce.Section6LocalCornerData

noncomputable section
open MeasureTheory Set
open scoped Convolution
namespace Luce.Section6

theorem convolutionDensity_pos65 {γ q : ℝ} (hγ : 0 < γ) (hq : 0 < q)
    (k : ℕ) (x : ℝ) : 0 < convolutionDensity γ q k x := by
  let p := incrementDensity γ q
  have hp := incrementDensity_traceDensity68 hγ hq
  induction k generalizing x with
  | zero => exact incrementDensity_pos hγ hq x
  | succ k ih =>
    change 0 < ∫ t : ℝ, p t * convolutionDensity γ q k (x-t)
    have hcont : Continuous (convolutionDensity γ q k) := by
      rw [← traceConvolution68_incrementDensity]
      exact hp.convolution_continuous k
    have hi : Integrable (fun t : ℝ => p t * convolutionDensity γ q k (x-t)) := by
      apply (hp.integrable.mul_const (γ*Real.exp (-1))).mono'
        (hp.continuous.mul (hcont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      filter_upwards [] with t
      change ‖incrementDensity γ q t * convolutionDensity γ q k (x-t)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (incrementDensity_pos hγ hq t) (ih _))]
      exact mul_le_mul_of_nonneg_left (convolutionDensity_bound hγ hq k (x-t)) (hp.nonneg t)
    rw [integral_pos_iff_support_of_nonneg (fun t =>
      (mul_pos (incrementDensity_pos hγ hq t) (ih _)).le) hi]
    have hs : Function.support (fun t : ℝ => p t * convolutionDensity γ q k (x-t)) = univ := by
      ext t
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (mul_pos (incrementDensity_pos hγ hq t) (ih _)).ne'
    rw [hs]
    simp

theorem cornerCoefficient_pos65 (side : Corner) (behavior : EndpointBehavior)
    (ha : behavior.active) (hγ : 0 < localCornerExponent behavior)
    (hq : 0 < localCornerQ side behavior) (k : ℕ) :
    0 < cornerCoefficient side behavior k := by
  cases behavior with
  | finite c => exact False.elim ha
  | power c γ η =>
    exact div_pos (convolutionDensity_pos65 hγ hq k 0) (by positivity)

theorem PowerProfile.cornerCoefficient_pos65 {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (side : Corner)
    (ha : (cornerBehavior left right side).active) (k : ℕ) :
    0 < cornerCoefficient side (cornerBehavior left right side) k := by
  obtain ⟨hγ,hq⟩ := hp.local_corner_parameters_pos side ha
  exact Luce.Section6.cornerCoefficient_pos65 side _ ha hγ hq k

theorem PowerProfile.cornerCoefficient_nonneg65 {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (side : Corner) (k : ℕ) :
    0 ≤ cornerCoefficient side (cornerBehavior left right side) k := by
  by_cases ha : (cornerBehavior left right side).active
  · exact (hp.cornerCoefficient_pos65 side ha k).le
  · cases h : cornerBehavior left right side with
    | finite c => simp [cornerCoefficient]
    | power c γ η => exact False.elim (ha (by simp [h, EndpointBehavior.active]))

theorem PowerProfile.totalCoefficient_pos65 {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (k : ℕ) : 0 < totalCoefficient left right k := by
  have hL := hp.cornerCoefficient_nonneg65 .left k
  have hR := hp.cornerCoefficient_nonneg65 .right k
  rcases hp.2.2.2.2 with h | h
  · have := hp.cornerCoefficient_pos65 .left h k
    exact add_pos_of_pos_of_nonneg this hR
  · have := hp.cornerCoefficient_pos65 .right h k
    exact add_pos_of_nonneg_of_pos hL this

end Luce.Section6
