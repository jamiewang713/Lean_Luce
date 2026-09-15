import Luce.Section6PowerWeightedSum

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem weighted_inverse_density_identity {a h : ℝ} (ha : 0 < a) (hh : 0 < h)
    (beta kappa d : ℝ) :
    (h/a)^kappa*((a/h)^beta/h)*Real.exp (-(d*(a/h)^beta)) =
      a^(-kappa)*(a^beta*h^(kappa-beta-1)*Real.exp (-(d*a^beta*h^(-beta)))) := by
  have h1 : (h/a)^kappa = a^(-kappa)*h^kappa := by
    rw [Real.div_rpow hh.le ha.le, Real.rpow_neg ha.le]
    ring
  have h2 : (a/h)^beta = a^beta*h^(-beta) := by
    rw [Real.div_rpow ha.le hh.le, Real.rpow_neg hh.le]
    ring
  have hpref : h^kappa*h^(-beta)/h = h^(kappa-beta-1) := by
    rw [Real.rpow_sub hh, Real.rpow_one, ← Real.rpow_add hh]
    congr 2
  rw [h1, h2]
  calc
    _ = a^(-kappa)*(a^beta*(h^kappa*h^(-beta)/h)*Real.exp (-(d*a^beta*h^(-beta)))) := by
      simp only [mul_assoc]
      ring
    _ = _ := by rw [hpref]

/-- The same-corner ordinary right row with the manuscript weight (h/a)^kappa.
The required integrability follows precisely from kappa<beta. -/
theorem right_ordinary_weighted_row_bound {beta kappa d : ℝ}
    (hb : 0 < beta) (hk : kappa < beta) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), ((h : ℝ)/a)^kappa*((a/(h : ℝ))^beta/(h : ℝ))*
      Real.exp (-(d*(a/(h : ℝ))^beta))) ≤ C := by
  have hq : 0 < ((kappa-beta-1)+1)/(-beta) :=
    div_pos_of_neg_of_neg (by linarith) (by linarith)
  obtain ⟨C, hC, hs⟩ := power_weighted_positive_sum_bound
    (a := kappa-beta-1) (p := -beta) (neg_ne_zero.mpr hb.ne') hq hd
  refine ⟨C, hC, ?_⟩
  intro a ha M
  have hscale : (a^beta)^(1-((kappa-beta-1)+1)/(-beta)) = a^kappa := by
    rw [← Real.rpow_mul ha.le]
    have he : beta*(1-((kappa-beta-1)+1)/(-beta)) = kappa := by field_simp; ring
    rw [he]
  have hsum := hs (a^beta) (Real.rpow_pos_of_pos ha _) M
  rw [hscale] at hsum
  have he : (∑ h ∈ Finset.Ico 1 (M+1), ((h : ℝ)/a)^kappa*((a/(h : ℝ))^beta/(h : ℝ))*
      Real.exp (-(d*(a/(h : ℝ))^beta))) =
      a^(-kappa)*(∑ h ∈ Finset.Ico 1 (M+1), a^beta*(h : ℝ)^(kappa-beta-1)*
        Real.exp (-(d*a^beta*(h : ℝ)^(-beta)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr (by have := (Finset.mem_Ico.mp hh).1; omega)
    exact weighted_inverse_density_identity ha hh0 beta kappa d
  rw [he]
  have hbound := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg ha.le (-kappa))
  have hcancel : a^(-kappa)*(C*a^kappa) = C := by
    rw [mul_left_comm, ← Real.rpow_add ha]
    simp
  exact hbound.trans_eq hcancel

end Luce.Section6
