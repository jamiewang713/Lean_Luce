import Luce.Section6ExceptionalWeightedRows
import Luce.Section6RightOrdinaryWeightedRow

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Complete right ordinary-plus-exceptional envelope weighted sum. -/
theorem right_envelope_weighted_sum_bound {beta v d nu kappa : ℝ}
    (hb : 0 < beta) (hv : 0 < v) (hd : 0 < d) (hnu : 0 < nu)
    (hk0 : 0 ≤ kappa) (hk : kappa < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ, 1 ≤ a → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), ((h : ℝ)/(a : ℝ))^kappa*
      ((((a : ℝ)/(h : ℝ))^beta/(h : ℝ))*Real.exp (-d*((a : ℝ)/(h : ℝ))^beta)+
        exceptionalEnvelope beta v d nu a h)) ≤ C := by
  obtain ⟨B, hB, hbrow⟩ := right_ordinary_weighted_row_bound hb hk hd
  obtain ⟨D, hD, he⟩ := right_exceptional_weighted_row_bound hb hv hd hnu hk0
  refine ⟨B+D, add_pos hB hD, ?_⟩
  intro a ha M
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hs := add_le_add (hbrow (a : ℝ) haR M) (he a ha M)
  simpa only [mul_add, Finset.sum_add_distrib, mul_assoc, neg_mul] using hs

end Luce.Section6
