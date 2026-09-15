import Luce.Section6SkeletonProduct
import Luce.Section6SelectedGapIntegral

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Fill the selected actual gap indices with independent integration
coordinates, leaving the supplied unselected coordinates fixed. -/
def selectedFill {n : ℕ} (S : Finset (Fin n)) (old : Fin n → ℝ)
    (fresh : ↥S → ℝ) (g : Fin n) : ℝ :=
  if h : g ∈ S then fresh ⟨g,h⟩ else old g

theorem selected_fill_selected {n : ℕ} (S : Finset (Fin n))
    (old : Fin n → ℝ) (fresh : ↥S → ℝ) (e : ↥S) :
    selectedFill S old fresh e = fresh e := by simp [selectedFill, e.property]

theorem skeleton_start_fill {n : ℕ} (w : Weights n) (sigma : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (q : Fin n) (old : Fin n → ℝ) (fresh : ↥S → ℝ) :
    skeletonStart w sigma S q (selectedFill S old fresh) = skeletonStart w sigma S q old := by
  apply skeleton_start_congr_unselected
  intro l hl
  simp [selectedFill, hl]

/-- Exact selected-coordinate integral for a fixed elimination chain and
fixed unselected spacings. Every rate and starting time is the existing
normalized-gap object. No insertion independence premise is used. -/
theorem selected_coordinate_integral {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (theta old : Fin n → ℝ)
    (ht : ∀ e ∈ S, 0 < theta e) :
    Integrable (fun fresh : ↥S → ℝ => ∏ e : ↥S,
      exponentialGapMass (theta e) (gapStartFromNormalized w sigma e (selectedFill S old fresh))
        (fresh e/orderedRemainingRate w sigma e)) (Measure.pi fun _ : ↥S => expMeasure 1) ∧
    (∫ fresh : ↥S → ℝ, ∏ e : ↥S,
      exponentialGapMass (theta e) (gapStartFromNormalized w sigma e (selectedFill S old fresh))
        (fresh e/orderedRemainingRate w sigma e) ∂Measure.pi (fun _ : ↥S => expMeasure 1)) =
      (∏ e : ↥S, Real.exp (-theta e*skeletonStart w sigma S e old)) *
      ∏ g : ↥S, orderedRemainingRate w sigma g * theta g /
        ((orderedRemainingRate w sigma g + laterSelectedRate S theta g) *
          (orderedRemainingRate w sigma g + laterSelectedRate S theta g + theta g)) := by
  classical
  let C := ∏ e : ↥S, Real.exp (-theta e*skeletonStart w sigma S e old)
  have he : (fun fresh : ↥S → ℝ => ∏ e : ↥S,
      exponentialGapMass (theta e) (gapStartFromNormalized w sigma e (selectedFill S old fresh))
        (fresh e/orderedRemainingRate w sigma e)) =
      (fun fresh => C * ∏ g : ↥S,
        (1-Real.exp (-theta g*(fresh g/orderedRemainingRate w sigma g))) *
          Real.exp (-laterSelectedRate S theta g*(fresh g/orderedRemainingRate w sigma g))) := by
    funext fresh
    have hp := selected_insertion_product_skeleton w sigma S theta (selectedFill S old fresh)
    rw [← Finset.prod_coe_sort S, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort S] at hp
    simpa only [selected_fill_selected, skeleton_start_fill] using hp
  have hi := selected_gaps_product_integral
    (fun g : ↥S => orderedRemainingRate w sigma g) (fun g : ↥S => theta g)
    (fun g : ↥S => laterSelectedRate S theta g)
    (fun g => orderedRemainingRate_pos w sigma g) (fun g => ht g g.property)
    (fun g => later_selected_rate_nonneg S theta (fun e he => (ht e he).le) g)
  rw [he]
  refine ⟨hi.1.const_mul C, ?_⟩
  rw [integral_const_mul, hi.2]

end Luce.Section6
