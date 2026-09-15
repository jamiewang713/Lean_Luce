import Luce.Section6SkeletonFubini

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace Luce.Section6

/-- The gap-index extension gives exactly the sum of original marked
rates at later selected gaps, with no contribution from other indices. -/
theorem later_selected_rate_reindex {n s : ℕ} (q : Fin s → Fin n) (hq : Injective q)
    (theta : Fin s → ℝ) (g : Fin n) :
    laterSelectedRate (Finset.univ.image q) (Function.extend q theta (fun _ => 0)) g =
      ∑ e ∈ Finset.univ.filter (fun e => g < q e), theta e := by
  classical
  unfold laterSelectedRate
  rw [Finset.filter_image, Finset.sum_image (fun a _ b _ h => hq h)]
  simp only [hq.extend_apply]

/-- Reindex marked rates by distinct actual selected gaps. The extension
away from the selected set is unused in every factor and later-rate sum. -/
theorem marked_normalized_skeleton_integral {n s : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (q : Fin s → Fin n) (hq : Injective q)
    (theta : Fin s → ℝ) (ht : ∀ e, 0 < theta e) :
    let S := Finset.univ.image q
    let thetaGap := Function.extend q theta (fun _ => 0)
    let split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun e => e ∈ S)
    (∫ xi, ∏ e, exponentialGapMass (theta e) (gapStartFromNormalized w sigma (q e) xi)
      (xi (q e)/orderedRemainingRate w sigma (q e)) ∂standardGapLaw n) =
    ∫ z : {e : Fin n // e ∉ S} → ℝ,
      (∏ e : ↥S, Real.exp (-thetaGap e * skeletonStart w sigma S e (split.symm (0,z)))) *
      ∏ g : ↥S, orderedRemainingRate w sigma g * thetaGap g /
        ((orderedRemainingRate w sigma g + laterSelectedRate S thetaGap g) *
          (orderedRemainingRate w sigma g + laterSelectedRate S thetaGap g + thetaGap g))
      ∂Measure.pi (fun _ : {e : Fin n // e ∉ S} => expMeasure 1) := by
  classical
  let S := Finset.univ.image q
  let thetaGap := Function.extend q theta (fun _ => 0)
  have htGap : ∀ e ∈ S, 0 < thetaGap e := by
    intro e he
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    simpa [thetaGap, hq.extend_apply] using ht a
  have he (xi : Fin n → ℝ) :
      (∏ e : ↥S, exponentialGapMass (thetaGap e) (gapStartFromNormalized w sigma e xi)
        (xi e/orderedRemainingRate w sigma e)) =
      ∏ e, exponentialGapMass (theta e) (gapStartFromNormalized w sigma (q e) xi)
        (xi (q e)/orderedRemainingRate w sigma (q e)) := by
    rw [Finset.prod_coe_sort S (fun e => exponentialGapMass (thetaGap e)
      (gapStartFromNormalized w sigma e xi) (xi e/orderedRemainingRate w sigma e))]
    dsimp [S]
    rw [Finset.prod_image (fun a _ b _ h => hq h)]
    simp only [thetaGap, hq.extend_apply]
  have hh := normalized_skeleton_integral w sigma S thetaGap htGap
  dsimp only at hh ⊢
  rw [← hh]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun xi => (he xi).symm)

end Luce.Section6
