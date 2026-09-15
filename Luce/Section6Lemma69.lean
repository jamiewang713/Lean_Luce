import Luce.Section6Lemma69Contract
import Luce.Section6CollisionFamilyBound
import Luce.Section6CollisionUnion

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Overlaps and nearby ranks, with both the specified-pair and all-pairs
conclusions. All constants are uniform in the population and core cutoffs. -/
theorem lemma69 : Lemma69Contract.lemma69 := by
  classical
  intro s L D C hC
  let C' := max 1 C
  let Q := C'^L
  let M := 2*(2*(D : ℝ)+1)*Q^2*Q^(s-1)
  let N : ℝ := (s*L : ℕ)
  let K := (N^2+1)*M
  have hC' : 1 ≤ C' := le_max_left _ _
  have hC'0 : 0 < C' := zero_lt_one.trans_le hC'
  have hQ : 0 < Q := pow_pos hC'0 _
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨K, mul_pos (by positivity) hM, ?_⟩
  intro n A B hA hAB side k hk F hF hrow htarget W hW
  have ha : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hrow' (a : Fin n) : (∑ b, F a b) ≤ C' := (hrow a).trans (le_max_right _ _)
  have htarget' (c : Fin s) (b : CollisionCore n A B (side c)) (a : Fin n) :
      F a b.val ≤ C'/(cornerDistance (side c) b.val : ℝ) :=
    (htarget c b a).trans (div_le_div_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _))
  let H := 1+Real.log ((B : ℝ)/A)
  let R := M/(A : ℝ)*H^(s-1)
  have hH : 0 ≤ H := by
    have hh : 0 ≤ Real.log ((B : ℝ)/A) := Real.log_nonneg ((one_le_div ha).mpr (by exact_mod_cast hAB))
    dsimp [H]; linarith
  have hR : 0 ≤ R := mul_nonneg (div_nonneg hM.le ha.le) (pow_nonneg hH _)
  have hfamily (p q : CollisionSlot k) (hpq : p ≠ q) :
      collisionPairSum (collisionFamilyWeight (A := A) (B := B) side k F) D p q ≤ R := by
    have hh := collision_family_pair_bound D hA hAB side k hk F hF hC' hrow' htarget' p q hpq
    apply hh.trans_eq
    dsimp [R, M, Q, H]
    rw [mul_pow]
    ring
  have hscale : R ≤ (N^2+1)*R := by nlinarith only [hR, sq_nonneg N]
  have he : (N^2+1)*R = K/(A : ℝ)*H^(s-1) := by dsimp [R, K]; ring
  constructor
  · intro p q hpq
    exact (collisionPairSum_mono hW D p q).trans ((hfamily p q hpq).trans (hscale.trans_eq he))
  · have hnon (x : CollisionAssignment n A B side k) : 0 ≤ collisionFamilyWeight side k F x :=
      Finset.prod_nonneg (fun c _ => collisionCycleWeight_nonneg
        (fun a b : CollisionCore n A B (side c) => hF a.val b.val) _ _)
    have hh := collision_union_le_card_sq (collisionFamilyWeight side k F) hnon D hR hfamily
    have hc : (Fintype.card (CollisionSlot k) : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast collision_slot_card_le k hk
    have hc2 : (Fintype.card (CollisionSlot k) : ℝ)^2 ≤ N^2+1 := by
      have hz : (0 : ℝ) ≤ Fintype.card (CollisionSlot k) := Nat.cast_nonneg _
      nlinarith only [hc, hz, sq_nonneg (N-(Fintype.card (CollisionSlot k) : ℝ))]
    exact (collisionUnionSum_mono hW D).trans (hh.trans
      ((mul_le_mul_of_nonneg_right hc2 hR).trans_eq he))

end Luce.Section6
