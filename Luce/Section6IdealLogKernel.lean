import Luce.Section6CycleExponentialMoment
import Luce.Section6LocalCornerData

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

def cornerLogDensity68 (side : Corner) (behavior : EndpointBehavior) (x : ℝ) : ℝ :=
  incrementDensity (localCornerExponent behavior) (localCornerQ side behavior)
    (match side with | .left => -x | .right => x)

theorem cornerLogDensity68_traceDensity (side : Corner) (behavior : EndpointBehavior)
    (hg : 0 < localCornerExponent behavior) (hq : 0 < localCornerQ side behavior) :
    TraceDensity68 (cornerLogDensity68 side behavior) := by
  cases side
  · exact (incrementDensity_traceDensity68 hg hq).reflect
  · exact incrementDensity_traceDensity68 hg hq

theorem cornerLogDensity68_envelope (side : Corner) (behavior : EndpointBehavior)
    (hg : 0 < localCornerExponent behavior) (hq : 0 < localCornerQ side behavior) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, cornerLogDensity68 side behavior x ≤
      C*Real.exp (-localCornerExponent behavior*|x|) := by
  obtain ⟨C, hC, hb⟩ := incrementDensity_exponential_envelope hg hq
  refine ⟨C, hC, ?_⟩
  intro x
  cases side
  · change incrementDensity (localCornerExponent behavior) (localCornerQ .left behavior) (-x) ≤ _
    have h := hb (-x)
    rw [abs_neg] at h
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans h
  · exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hb x)

theorem localIdealKernel_log68 (side : Corner) (behavior : EndpointBehavior)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    localIdealKernel side behavior a b =
      cornerLogDensity68 side behavior (Real.log (a : ℝ)-Real.log (b : ℝ))/(b : ℝ) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have he : localCornerRatio side behavior a b =
      Real.exp (localCornerExponent behavior*
        (match side with
        | .left => -(Real.log (a : ℝ)-Real.log (b : ℝ))
        | .right => Real.log (a : ℝ)-Real.log (b : ℝ))) := by
    cases side <;> unfold localCornerRatio
    · rw [Real.rpow_def_of_pos (div_pos hbR haR), Real.log_div hbR.ne' haR.ne']
      congr 1
      ring
    · rw [Real.rpow_def_of_pos (div_pos haR hbR), Real.log_div haR.ne' hbR.ne']
      congr 1
      ring
  unfold localIdealKernel cornerLogDensity68 incrementDensity
  rw [he]
  ring

theorem cornerCoefficient_logDensity68 (side : Corner) (behavior : EndpointBehavior)
    (hactive : behavior.active) (k : ℕ) :
    cornerCoefficient side behavior k =
      traceConvolution68 (cornerLogDensity68 side behavior) k 0/((k : ℝ)+1) := by
  cases behavior with
  | finite c => exact False.elim hactive
  | power c gamma eta =>
    cases side
    · rw [show cornerLogDensity68 .left (.power c gamma eta) =
          (fun x => incrementDensity gamma (localCornerQ .left (.power c gamma eta)) (-x)) from rfl,
        traceConvolution68_reflect, neg_zero, traceConvolution68_incrementDensity]
      rfl
    · rw [show cornerLogDensity68 .right (.power c gamma eta) =
          incrementDensity gamma (localCornerQ .right (.power c gamma eta)) from rfl,
        traceConvolution68_incrementDensity]
      rfl

theorem idealCycleWeight_log68 (side : Corner) (behavior : EndpointBehavior)
    (k : ℕ) (a : Fin (k+1) → ℕ) (ha : ∀ j, 0 < a j) :
    idealCycleWeight side behavior k a =
      closedLogCycleWeight (cornerLogDensity68 side behavior) k (fun j => Real.log (a j : ℝ))*
        ∏ j, (1/(a j : ℝ)) := by
  unfold idealCycleWeight closedLogCycleWeight
  simp_rw [localIdealKernel_log68 side behavior (ha _) (ha _), div_eq_mul_inv]
  rw [Finset.prod_mul_distrib]
  congr 1
  simpa only [one_mul] using Equiv.prod_comp (finRotate (k+1)) (fun j => (a j : ℝ)⁻¹)

end Luce.Section6
