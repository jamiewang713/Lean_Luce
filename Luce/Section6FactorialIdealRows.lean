import Luce.Section6FactorialKernelRows

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem local_ideal_matrix_bounds (side : Corner) (behavior : EndpointBehavior)
    {kappa : ℝ} (hq : 0 < localCornerQ side behavior) (hg : 0 < localCornerExponent behavior)
    (hk : kappa < localCornerExponent behavior) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ n (a b : Fin n), 0 ≤ localIdealKernel side behavior
        (cornerDistance side a) (cornerDistance side b)) ∧
      (∀ n (a : Fin n), (∑ b : Fin n, localIdealKernel side behavior
        (cornerDistance side a) (cornerDistance side b)) ≤ C) ∧
      (∀ n (a b : Fin n), localIdealKernel side behavior
        (cornerDistance side a) (cornerDistance side b) ≤ C/(cornerDistance side b : ℝ)) ∧
      (∀ n (a : Fin n), (∑ b : Fin n,
        (cornerRowRatio side (cornerDistance side a) (cornerDistance side b))^kappa *
          localIdealKernel side behavior (cornerDistance side a) (cornerDistance side b)) ≤ C) := by
  obtain ⟨C, hC, hF, hr, ht, hw⟩ := local_envelope_matrix_bounds side behavior hq hg hk
  let c := localCornerExponent behavior*localCornerQ side behavior
  have hc : 0 < c := mul_pos hg hq
  refine ⟨max 1 (c*C), le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · intro n a b
    rw [local_ideal_eq_scaled_envelope]
    exact mul_nonneg hc.le (hF n a b)
  · intro n a
    simp_rw [local_ideal_eq_scaled_envelope]
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hr n a) hc.le).trans (le_max_right _ _)
  · intro n a b
    rw [local_ideal_eq_scaled_envelope]
    have hh := mul_le_mul_of_nonneg_left (ht n a b) hc.le
    have hb : c*(C/(cornerDistance side b : ℝ)) ≤ max 1 (c*C)/(cornerDistance side b : ℝ) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)
    exact hh.trans hb
  · intro n a
    have he : (∑ b : Fin n,
        (cornerRowRatio side (cornerDistance side a) (cornerDistance side b))^kappa *
          localIdealKernel side behavior (cornerDistance side a) (cornerDistance side b)) =
        c*(∑ b : Fin n,
          (cornerRowRatio side (cornerDistance side a) (cornerDistance side b))^kappa *
            localEnvelopeKernel side behavior (localCornerQ side behavior)
              (cornerDistance side a) (cornerDistance side b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b _
      rw [local_ideal_eq_scaled_envelope]
      dsimp [c]
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left (hw n a) hc.le).trans (le_max_right _ _)

end Luce.Section6
