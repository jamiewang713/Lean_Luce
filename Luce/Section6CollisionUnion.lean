import Luce.Section6CollisionDefinitions

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem collision_same_corner_distance {n : ℕ} (side : Corner) (a b : Fin n) :
    Nat.dist (cornerDistance side a) (cornerDistance side b) = Nat.dist a.val b.val := by
  cases side <;> simp only [cornerDistance, Nat.dist] <;> omega

theorem collision_slot_card_le {s L : ℕ} (k : Fin s → ℕ) (hk : ∀ c, k c+1 ≤ L) :
    Fintype.card (CollisionSlot k) ≤ s*L := by
  calc
    _ = ∑ c, (k c+1) := by simp [CollisionSlot, Fintype.card_sigma]
    _ ≤ ∑ _c : Fin s, L := Finset.sum_le_sum (fun c _ => hk c)
    _ = _ := by simp

theorem collisionPairSum_mono {s n A B : ℕ} {side : Fin s → Corner} {k : Fin s → ℕ}
    {W V : CollisionAssignment n A B side k → ℝ} (h : ∀ x, W x ≤ V x)
    (D : ℕ) (p q : CollisionSlot k) : collisionPairSum W D p q ≤ collisionPairSum V D p q :=
  Finset.sum_le_sum (fun x _ => h x)

theorem collisionUnionSum_mono {s n A B : ℕ} {side : Fin s → Corner} {k : Fin s → ℕ}
    {W V : CollisionAssignment n A B side k → ℝ} (h : ∀ x, W x ≤ V x)
    (D : ℕ) : collisionUnionSum W D ≤ collisionUnionSum V D :=
  Finset.sum_le_sum (fun x _ => h x)

theorem collision_union_le_card_sq {s n A B : ℕ} {side : Fin s → Corner} {k : Fin s → ℕ}
    (W : CollisionAssignment n A B side k → ℝ) (hW : ∀ x, 0 ≤ W x) (D : ℕ)
    {R : ℝ} (hR : 0 ≤ R)
    (hpair : ∀ p q : CollisionSlot k, p ≠ q → collisionPairSum W D p q ≤ R) :
    collisionUnionSum W D ≤ (Fintype.card (CollisionSlot k) : ℝ)^2*R := by
  classical
  unfold collisionUnionSum
  rw [Finset.sum_filter]
  calc
    _ ≤ ∑ x : CollisionAssignment n A B side k, ∑ p : CollisionSlot k, ∑ q : CollisionSlot k,
        if p ≠ q ∧ collisionNearby D p q x then W x else 0 := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs with he
      · obtain ⟨p, q, hpq, hh⟩ := he
        have hinner : W x ≤ ∑ q' : CollisionSlot k,
            if p ≠ q' ∧ collisionNearby D p q' x then W x else 0 := by
          have h := Finset.single_le_sum (s := Finset.univ)
            (f := fun q' => if p ≠ q' ∧ collisionNearby D p q' x then W x else 0)
            (fun q' _ => by split_ifs <;> first | exact hW x | exact le_rfl) (Finset.mem_univ q)
          simpa only [if_pos (And.intro hpq hh)] using h
        exact hinner.trans (Finset.single_le_sum
          (f := fun p' => ∑ q' : CollisionSlot k, if p' ≠ q' ∧ collisionNearby D p' q' x then W x else 0)
          (fun p' _ => Finset.sum_nonneg (fun q' _ => by split_ifs <;> first | exact hW x | exact le_rfl))
          (Finset.mem_univ p))
      · exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg
          (fun q _ => by split_ifs <;> first | exact hW x | exact le_rfl))
    _ = ∑ p : CollisionSlot k, ∑ q : CollisionSlot k, ∑ x : CollisionAssignment n A B side k,
        if p ≠ q ∧ collisionNearby D p q x then W x else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro p _; rw [Finset.sum_comm]
    _ ≤ ∑ _p : CollisionSlot k, ∑ _q : CollisionSlot k, R := by
      apply Finset.sum_le_sum; intro p _
      apply Finset.sum_le_sum; intro q _
      by_cases hpq : p = q
      · subst q; simpa using hR
      · simpa [collisionPairSum, Finset.sum_filter, hpq] using hpair p q hpq
    _ = _ := by simp; ring

end Luce.Section6
