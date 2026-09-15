import Luce.Section6SelectedGapReindex
import Luce.Section6SeparatedOrderSum

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace Luce.Section6

/-- Exact skeleton formula for the actual separated cylinder. Both the
elimination-order mixture and the unselected-spacing integration use the
existing race law; no conditional independence premise is supplied. -/
theorem separated_cylinder_skeleton_formula {n s r : ℕ} (w : Weights n) (hs : s ≤ r)
    (u j : Fin s → Fin n) (hu : Injective u) (hj : Injective j)
    (hsep : ∀ a b, a ≠ b → 2*r < Nat.dist (j a).val (j b).val)
    (hbuffer : ∀ e, r < n-(j e).val) :
    let removed := Finset.univ.image (u ∘ Tuple.sort j)
    let N := (Finset.univ \ removed).card
    let q : Fin s → Fin N := fun e =>
      ⟨sortedMarkedGapIndex j e, sorted_gap_nonfinal_of_terminal_buffer hs u j hu hj hbuffer e⟩
    let S := Finset.univ.image q
    let thetaGap := Function.extend q (fun e => w.rate (u (Tuple.sort j e))) (fun _ => 0)
    let cw := compactDeletedWeights w removed
    let split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (fun e => e ∈ S)
    (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} =
      ∑ sigma : Equiv.Perm (Fin N), cw.mass sigma *
        (∫ z : {e : Fin N // e ∉ S} → ℝ,
          (∏ e : ↥S, Real.exp (-thetaGap e * skeletonStart cw sigma S e (split.symm (0,z)))) *
          ∏ g : ↥S, orderedRemainingRate cw sigma g * thetaGap g /
            ((orderedRemainingRate cw sigma g + laterSelectedRate S thetaGap g) *
              (orderedRemainingRate cw sigma g + laterSelectedRate S thetaGap g + thetaGap g))
          ∂Measure.pi (fun _ : {e : Fin N // e ∉ S} => expMeasure 1)) := by
  classical
  dsimp only
  rw [separated_cylinder_order_sum w hs u j hu hj hsep hbuffer]
  apply Finset.sum_congr rfl
  intro sigma _
  congr 1
  apply marked_normalized_skeleton_integral
  · intro a b hab
    apply sorted_gap_injective_of_separated hs j hj hsep
    exact congrArg Fin.val hab
  · intro e
    exact w.positive _

end Luce.Section6
