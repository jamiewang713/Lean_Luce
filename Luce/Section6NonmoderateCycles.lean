import Luce.Section6CornerPotential
import Luce.Section6WeightedCycleEdges
import Luce.Section6CollisionCoreTests

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem core_potential_row {n A B : ℕ} (side : Corner) (kappa : ℝ)
    (F : Fin n → Fin n → ℝ) (hF : ∀ a b, 0 ≤ F a b) {C : ℝ}
    (hw : ∀ a, (∑ b, (cornerRowRatio side (cornerDistance side a) (cornerDistance side b))^kappa *
      F a b) ≤ C) (a : CollisionCore n A B side) :
    (∑ b : CollisionCore n A B side, F a.val b.val*
      cornerDepthPotential side kappa (cornerDistance side b.val)) ≤
      C*cornerDepthPotential side kappa (cornerDistance side a.val) := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image (Subtype.val : CollisionCore n A B side → Fin n),
        F a.val b*cornerDepthPotential side kappa (cornerDistance side b) :=
      (Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)).symm
    _ ≤ ∑ b : Fin n, F a.val b*cornerDepthPotential side kappa (cornerDistance side b) :=
      Finset.sum_le_univ_sum_of_nonneg (fun b => mul_nonneg (hF a.val b)
        (corner_potential_pos side kappa (cornerDistance_positive side b)).le)
    _ ≤ _ := corner_weighted_row_to_potential side kappa F hw a.val

/-- A single nonmoderate edge costs a negative power of the lower core
cutoff, for the actual domination matrix as well as ideal kernels. -/
theorem nonmoderate_cycle_edge_sum {n A B k L : ℕ} (side : Corner) (behavior : EndpointBehavior)
    (hA : 1 ≤ A) (hAB : A ≤ B) (F : Fin n → Fin n → ℝ) (hF : ∀ a b, 0 ≤ F a b)
    {C v kappa eta : ℝ} (hC : 1 ≤ C) (hv : 0 < v) (hk : 0 < kappa)
    (hg : 0 < localCornerExponent behavior) (heta : eta ≤ v*kappa/localCornerExponent behavior)
    (hL : k+1 ≤ L)
    (hw : ∀ a, (∑ b, (cornerRowRatio side (cornerDistance side a) (cornerDistance side b))^kappa *
      F a b) ≤ C)
    (ht : ∀ (b : CollisionCore n A B side) a, F a b.val ≤ C/(cornerDistance side b.val : ℝ))
    (i : Fin (k+1)) :
    (∑ x ∈ Finset.univ.filter (fun x : Fin (k+1) → CollisionCore n A B side =>
      ¬ localCornerRatio side behavior (cornerDistance side (x i).val)
        (cornerDistance side (x (finRotate (k+1) i)).val) ≤
          (min (cornerDistance side (x i).val : ℝ)
            (cornerDistance side (x (finRotate (k+1) i)).val : ℝ))^v),
      collisionCycleWeight (fun a b => F a.val b.val) k x) ≤
        (C^L*(1+Real.log ((B : ℝ)/A)))/(A : ℝ)^eta := by
  let V (a : CollisionCore n A B side) := cornerDepthPotential side kappa (cornerDistance side a.val)
  have hV (a : CollisionCore n A B side) : 0 < V a :=
    corner_potential_pos side kappa (cornerDistance_positive side a.val)
  have hQ : 0 < (A : ℝ)^eta := Real.rpow_pos_of_pos
    (by exact_mod_cast (show 0 < A by omega)) eta
  have hh := cycle_large_edge_potential_bound (fun a b : CollisionCore n A B side => F a.val b.val)
    (fun a b => hF a.val b.val) V hV (fun a => 1/(cornerDistance side a.val : ℝ))
    (fun _ => by positivity) (zero_le_one.trans hC) hQ (core_potential_row side kappa F hF hw)
    (fun a b => by simpa [div_eq_mul_inv] using ht b a.val) k i
  calc
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin (k+1) → CollisionCore n A B side =>
        (A : ℝ)^eta ≤ V (x i)/V (x (finRotate (k+1) i))),
        collisionCycleWeight (fun a b => F a.val b.val) k x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact nonmoderate_edge_has_large_potential side behavior hA (x i).property.1
          (x (finRotate (k+1) i)).property.1 hv hk hg heta (Finset.mem_filter.mp hx).2
      · intro x _ _
        exact collisionCycleWeight_nonneg (fun a b => hF a.val b.val) k x
    _ ≤ _ := hh.trans (div_le_div_of_nonneg_right
      (mul_le_mul (pow_le_pow_right₀ hC hL) (collision_core_harmonic side hA hAB)
        (Finset.sum_nonneg (fun _ _ => by positivity)) (pow_nonneg (zero_le_one.trans hC) L)) hQ.le)

end Luce.Section6
