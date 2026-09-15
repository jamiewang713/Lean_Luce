import Luce.Section6RightOrdinaryWeightedRow
import Luce.Section6ActiveOrdinaryRows

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem weighted_forward_density_identity {a h : ℝ} (ha : 0 < a) (hh : 0 < h)
    (alpha kappa d : ℝ) :
    (a/h)^kappa*((h/a)^alpha/h)*Real.exp (-(d*(h/a)^alpha)) =
      a^kappa*(a^(-alpha)*h^(alpha-kappa-1)*Real.exp (-(d*a^(-alpha)*h^alpha))) := by
  have he := weighted_inverse_density_identity ha hh (-alpha) (-kappa) d
  simp only [neg_neg] at he
  rw [← reverse_ratio_power ha hh kappa, ← reverse_ratio_power hh ha alpha] at he
  simpa only [show -kappa - -alpha - 1 = alpha-kappa-1 by ring] using he

/-- The local ordinary left row with the manuscript weight (a/h)^kappa.
Its integrability at zero is discharged by kappa<alpha. -/
theorem left_ordinary_weighted_row_bound {alpha kappa d : ℝ}
    (ha : 0 < alpha) (hk : kappa < alpha) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), (a/(h : ℝ))^kappa*(((h : ℝ)/a)^alpha/(h : ℝ))*
      Real.exp (-(d*((h : ℝ)/a)^alpha))) ≤ C := by
  have hq : 0 < ((alpha-kappa-1)+1)/alpha := div_pos (by linarith) ha
  obtain ⟨C, hC, hs⟩ := power_weighted_positive_sum_bound
    (a := alpha-kappa-1) ha.ne' hq hd
  refine ⟨C, hC, ?_⟩
  intro a ha0 M
  have hscale : (a^(-alpha))^(1-((alpha-kappa-1)+1)/alpha) = a^(-kappa) := by
    rw [← Real.rpow_mul ha0.le]
    have he : (-alpha)*(1-((alpha-kappa-1)+1)/alpha) = -kappa := by field_simp; ring
    rw [he]
  have hsum := hs (a^(-alpha)) (Real.rpow_pos_of_pos ha0 _) M
  rw [hscale] at hsum
  have he : (∑ h ∈ Finset.Ico 1 (M+1), (a/(h : ℝ))^kappa*(((h : ℝ)/a)^alpha/(h : ℝ))*
      Real.exp (-(d*((h : ℝ)/a)^alpha))) =
      a^kappa*(∑ h ∈ Finset.Ico 1 (M+1), a^(-alpha)*(h : ℝ)^(alpha-kappa-1)*
        Real.exp (-(d*a^(-alpha)*(h : ℝ)^alpha))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr (by have := (Finset.mem_Ico.mp hh).1; omega)
    exact weighted_forward_density_identity ha0 hh0 alpha kappa d
  rw [he]
  have hbound := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg ha0.le kappa)
  have hcancel : a^kappa*(C*a^(-kappa)) = C := by
    rw [mul_left_comm, ← Real.rpow_add ha0]
    simp
  exact hbound.trans_eq hcancel

end Luce.Section6
