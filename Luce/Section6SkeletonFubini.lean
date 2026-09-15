import Luce.Section6SelectedCoordinateIntegral
import Luce.Section6NormalizedProductIntegrability

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Integrate the selected coordinates of the full normalized gap law.
The unselected-coordinate measure is the actual marginal product law. -/
theorem normalized_skeleton_integral {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (theta : Fin n → ℝ)
    (ht : ∀ e ∈ S, 0 < theta e) :
    let split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun e => e ∈ S)
    (∫ xi, ∏ e : ↥S, exponentialGapMass (theta e)
      (gapStartFromNormalized w sigma e xi)
      (xi e/orderedRemainingRate w sigma e) ∂standardGapLaw n) =
    ∫ z : {e : Fin n // e ∉ S} → ℝ,
      (∏ e : ↥S, Real.exp (-theta e * skeletonStart w sigma S e (split.symm (0,z)))) *
      ∏ g : ↥S, orderedRemainingRate w sigma g * theta g /
        ((orderedRemainingRate w sigma g + laterSelectedRate S theta g) *
          (orderedRemainingRate w sigma g + laterSelectedRate S theta g + theta g))
      ∂Measure.pi (fun _ : {e : Fin n // e ∉ S} => expMeasure 1) := by
  classical
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  let split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun e => e ∈ S)
  let H := fun xi => ∏ e : ↥S, exponentialGapMass (theta e)
    (gapStartFromNormalized w sigma e xi) (xi e/orderedRemainingRate w sigma e)
  have hi : Integrable H (standardGapLaw n) :=
    normalized_insertion_product_integrable w sigma (fun e : ↥S => e.val)
      (fun e : ↥S => theta e) (fun e => (ht e e.property).le)
  have hp := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin n => expMeasure 1) (fun e => e ∈ S)
  have hs := hp.symm split
  have hcomp := hs.integrable_comp_of_integrable hi
  change (∫ xi, H xi ∂standardGapLaw n) = _
  rw [standardGapLaw, ← hs.integral_comp' H]
  rw [integral_prod_symm (fun x => H (split.symm x)) hcomp]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have he (fresh : ↥S → ℝ) :
      split.symm (fresh,z) = selectedFill S (split.symm (0,z)) fresh := by
    ext e
    by_cases h : e ∈ S <;>
      simp [split, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
        selectedFill, h]
  have hh := (selected_coordinate_integral w sigma S theta (split.symm (0,z)) ht).2
  have hfun : (fun fresh : ↥S → ℝ => H (split.symm (fresh,z))) =
      (fun fresh : ↥S → ℝ => ∏ e : ↥S, exponentialGapMass (theta e)
        (gapStartFromNormalized w sigma e (selectedFill S (split.symm (0,z)) fresh))
        (fresh e/orderedRemainingRate w sigma e)) := by
    funext fresh
    dsimp only [H]
    rw [he fresh]
    simp only [selected_fill_selected]
  convert (congrArg (fun F : (↥S → ℝ) → ℝ =>
    ∫ fresh, F fresh ∂Measure.pi (fun _ : ↥S => expMeasure 1)) hfun).trans hh using 1
  dsimp only
  congr
  exact Subsingleton.elim _ _

end Luce.Section6
