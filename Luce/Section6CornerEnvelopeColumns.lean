import Luce.Section6ActiveOrdinaryColumns
import Luce.Section6ExceptionalWeightedRows

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- The complete right ordinary-plus-exceptional envelope has uniformly
bounded columns. All summability is proved, not assumed. -/
theorem right_corner_envelope_column_bound {beta v d nu : ℝ}
    (hb : 0 < beta) (hv : 0 < v) (hd : 0 < d) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 1 ≤ h → ∀ M : ℕ,
      (∑ a ∈ Finset.Ico 1 (M+1),
        ((((a : ℝ)/(h : ℝ))^beta/(h : ℝ))*Real.exp (-d*((a : ℝ)/(h : ℝ))^beta)+
          exceptionalEnvelope beta v d nu a h)) ≤ C := by
  obtain ⟨B, hB, hbnd⟩ := right_ordinary_column_bound hb hd
  obtain ⟨D, hD, hdnd⟩ := left_exceptional_weighted_row_bound hb hv hd hnu (kappa := 0) le_rfl
  refine ⟨B+D, add_pos hB hD, ?_⟩
  intro h hh M
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have ho : (∑ a ∈ Finset.Ico 1 (M+1),
      (((a : ℝ)/(h : ℝ))^beta/(h : ℝ))*Real.exp (-d*((a : ℝ)/(h : ℝ))^beta)) ≤ B := by
    have ht := div_le_div_of_nonneg_right (hbnd (h : ℝ) hhR M) hhR.le
    simpa only [neg_mul, div_mul_eq_mul_div, ← Finset.sum_div, mul_div_cancel_right₀ B hhR.ne'] using ht
  have he : (∑ a ∈ Finset.Ico 1 (M+1), exceptionalEnvelope beta v d nu a h) ≤ D := by
    simpa only [Real.rpow_zero, one_mul] using hdnd h hh M
  rw [Finset.sum_add_distrib]
  exact add_le_add ho he

/-- The complete left envelope, including its transposed exceptional term,
has uniformly bounded columns under the manuscript's alpha>1. -/
theorem left_corner_envelope_column_bound {alpha v d nu : ℝ}
    (ha : 1 < alpha) (hv : 0 < v) (hd : 0 < d) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 1 ≤ h → ∀ M : ℕ,
      (∑ a ∈ Finset.Ico 1 (M+1),
        ((((h : ℝ)/(a : ℝ))^alpha/(h : ℝ))*Real.exp (-d*((h : ℝ)/(a : ℝ))^alpha)+
          exceptionalEnvelope alpha v d nu h a)) ≤ C := by
  obtain ⟨B, hB, hbnd⟩ := left_ordinary_column_bound ha hd
  obtain ⟨D, hD, hdnd⟩ := right_exceptional_weighted_row_bound
    (zero_lt_one.trans ha) hv hd hnu (kappa := 0) le_rfl
  refine ⟨B+D, add_pos hB hD, ?_⟩
  intro h hh M
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have ho : (∑ a ∈ Finset.Ico 1 (M+1),
      (((h : ℝ)/(a : ℝ))^alpha/(h : ℝ))*Real.exp (-d*((h : ℝ)/(a : ℝ))^alpha)) ≤ B := by
    have ht := div_le_div_of_nonneg_right (hbnd (h : ℝ) hhR M) hhR.le
    simpa only [neg_mul, div_mul_eq_mul_div, ← Finset.sum_div, mul_div_cancel_right₀ B hhR.ne'] using ht
  have he : (∑ a ∈ Finset.Ico 1 (M+1), exceptionalEnvelope alpha v d nu h a) ≤ D := by
    simpa only [Real.rpow_zero, one_mul] using hdnd h hh M
  rw [Finset.sum_add_distrib]
  exact add_le_add ho he

end Luce.Section6
