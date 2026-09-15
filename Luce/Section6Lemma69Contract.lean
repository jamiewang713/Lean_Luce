import Luce.Section6CollisionDefinitions

/-! Independent contract for manuscript Lemma 6.9. The only matrix
hypotheses are its nonnegativity, bounded rows and the stated target
bound on each core. No separation of the two endpoint cores is assumed. -/
noncomputable section
open scoped BigOperators
namespace Luce.Section6.Lemma69Contract

def lemma69 : Prop :=
  ∀ (s L D : ℕ) (C : ℝ), 0 < C → ∃ K : ℝ, 0 < K ∧
    ∀ (n A B : ℕ), 1 ≤ A → A ≤ B →
    ∀ (side : Fin s → Corner) (k : Fin s → ℕ), (∀ c, k c+1 ≤ L) →
    ∀ F : Fin n → Fin n → ℝ, (∀ a b, 0 ≤ F a b) →
    (∀ a, ∑ b, F a b ≤ C) →
    (∀ c (b : CollisionCore n A B (side c)) a,
      F a b.val ≤ C/(cornerDistance (side c) b.val : ℝ)) →
    ∀ W : CollisionAssignment n A B side k → ℝ,
      (∀ x, W x ≤ collisionFamilyWeight side k F x) →
      (∀ p q : CollisionSlot k, p ≠ q →
        collisionPairSum W D p q ≤ K/(A : ℝ)*(1+Real.log ((B : ℝ)/A))^(s-1)) ∧
      collisionUnionSum W D ≤ K/(A : ℝ)*(1+Real.log ((B : ℝ)/A))^(s-1)

end Luce.Section6.Lemma69Contract
