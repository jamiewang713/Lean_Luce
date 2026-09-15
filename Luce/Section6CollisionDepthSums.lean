import Luce.Section6CollisionDefinitions
import Luce.Section6LogExcursionAlgebra

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem collision_core_depth_sum_le {n A B : ℕ} (side : Corner)
    (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m) :
    (∑ v : CollisionCore n A B side, f (cornerDistance side v.val)) ≤
      ∑ m ∈ Finset.Icc A B, f m := by
  classical
  let d : CollisionCore n A B side → ℕ := fun v => cornerDistance side v.val
  have hd : Function.Injective d := fun a b h =>
    Subtype.ext (cornerDistance_injective67 side h)
  calc
    _ = ∑ m ∈ Finset.univ.image d, f m := (Finset.sum_image (fun a _ b _ h => hd h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro m hm; obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hm; exact Finset.mem_Icc.mpr v.property)
      (fun m _ _ => hf m)

theorem collision_core_harmonic {n A B : ℕ} (side : Corner) (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ v : CollisionCore n A B side, 1/(cornerDistance side v.val : ℝ)) ≤
      1+Real.log ((B : ℝ)/A) :=
  (collision_core_depth_sum_le side (fun m => 1/(m : ℝ)) (fun _ => by positivity)).trans
    (harmonic_interval_sum67 hA hAB)

theorem collision_core_square_sum {n A B : ℕ} (side : Corner) (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ v : CollisionCore n A B side, (1/(cornerDistance side v.val : ℝ))^2) ≤ 2/(A : ℝ) := by
  have ha : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hs := left_excursion_depth_sum (kappa := 1) (by norm_num) hA hAB
  norm_num [Real.rpow_neg, Real.rpow_two, one_div] at hs
  apply (collision_core_depth_sum_le side (fun m => (1/(m : ℝ))^2) (fun _ => sq_nonneg _)).trans
  apply (le_div_iff₀ ha).mpr
  simpa [mul_comm, one_div, inv_pow] using hs

theorem collision_nearby_card {n A B : ℕ} (side : Corner) (a : Fin n) (D : ℕ) :
    (Finset.univ.filter (fun b : CollisionCore n A B side => Nat.dist a.val b.val.val ≤ D)).card ≤
      2*D+1 := by
  classical
  let S := Finset.univ.filter (fun b : CollisionCore n A B side => Nat.dist a.val b.val.val ≤ D)
  have hi : Function.Injective (fun b : CollisionCore n A B side => b.val.val) := by
    intro x y h; exact Subtype.ext (Fin.ext h)
  have hsub : S.image (fun b => b.val.val) ⊆ Finset.Icc (a.val-D) (a.val+D) := by
    intro m hm
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
    have := (Finset.mem_filter.mp hb).2
    simp only [Nat.dist] at this
    exact Finset.mem_Icc.mpr (by omega)
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective S hi, Nat.card_Icc] at hh
  change S.card ≤ _
  omega

/-- The mixed-corner case also follows from bounded nearby-label fibres.
No disjointness or asymptotic separation of the endpoint cores is needed. -/
theorem collision_nearby_reciprocal_sum {n A B : ℕ} (side side' : Corner)
    (hA : 1 ≤ A) (hAB : A ≤ B) (D : ℕ) :
    (∑ a : CollisionCore n A B side, ∑ b : CollisionCore n A B side',
      if Nat.dist a.val.val b.val.val ≤ D then
        (1/(cornerDistance side a.val : ℝ))*(1/(cornerDistance side' b.val : ℝ)) else 0) ≤
      2*(2*(D : ℝ)+1)/(A : ℝ) := by
  classical
  let u : CollisionCore n A B side → ℝ := fun a => 1/(cornerDistance side a.val : ℝ)
  let v : CollisionCore n A B side' → ℝ := fun b => 1/(cornerDistance side' b.val : ℝ)
  have hfirst : (∑ a : CollisionCore n A B side, ∑ b : CollisionCore n A B side',
      if Nat.dist a.val.val b.val.val ≤ D then (u a)^2 else 0) ≤
      (2*(D : ℝ)+1)*(2/(A : ℝ)) := by
    calc
      _ ≤ ∑ a : CollisionCore n A B side, (2*(D : ℝ)+1)*(u a)^2 := by
        apply Finset.sum_le_sum; intro a _
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast collision_nearby_card side' a.val D) (sq_nonneg _)
      _ = (2*(D : ℝ)+1)*∑ a : CollisionCore n A B side, (u a)^2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (collision_core_square_sum side hA hAB) (by positivity)
  have hsecond : (∑ a : CollisionCore n A B side, ∑ b : CollisionCore n A B side',
      if Nat.dist a.val.val b.val.val ≤ D then (v b)^2 else 0) ≤
      (2*(D : ℝ)+1)*(2/(A : ℝ)) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ b : CollisionCore n A B side', (2*(D : ℝ)+1)*(v b)^2 := by
        apply Finset.sum_le_sum; intro b _
        simp_rw [Nat.dist_comm _ b.val.val]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast collision_nearby_card side b.val D) (sq_nonneg _)
      _ = (2*(D : ℝ)+1)*∑ b : CollisionCore n A B side', (v b)^2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (collision_core_square_sum side' hA hAB) (by positivity)
  have hpoint : (∑ a : CollisionCore n A B side, ∑ b : CollisionCore n A B side',
      if Nat.dist a.val.val b.val.val ≤ D then 2*(u a*v b) else 0) ≤
      (∑ a : CollisionCore n A B side, ∑ b : CollisionCore n A B side',
      if Nat.dist a.val.val b.val.val ≤ D then (u a)^2 else 0) +
      (∑ a : CollisionCore n A B side, ∑ b : CollisionCore n A B side',
      if Nat.dist a.val.val b.val.val ≤ D then (v b)^2 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro b _
    split_ifs <;> nlinarith [sq_nonneg (u a-v b)]
  have he : (∑ a : CollisionCore n A B side, ∑ b : CollisionCore n A B side',
      if Nat.dist a.val.val b.val.val ≤ D then 2*(u a*v b) else 0) =
      2*(∑ a : CollisionCore n A B side, ∑ b : CollisionCore n A B side',
      if Nat.dist a.val.val b.val.val ≤ D then u a*v b else 0) := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [he] at hpoint
  change (∑ a, ∑ b, if Nat.dist a.val.val b.val.val ≤ D then u a*v b else 0) ≤ _
  calc
    _ ≤ (2*(D : ℝ)+1)*(2/(A : ℝ)) := by linarith only [hpoint, hfirst, hsecond]
    _ = _ := by ring

end Luce.Section6
