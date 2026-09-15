import Luce.Section6ExceptionalWeightedRows
import Luce.Section6LeftOrdinaryWeightedRow

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Both ordinary and exceptional terms of the left insertion envelope
have a uniform weighted row sum. Every summability premise is proved. -/
theorem left_envelope_weighted_sum_bound {alpha v d nu kappa : ℝ}
    (ha : 0 < alpha) (hv : 0 < v) (hd : 0 < d) (hnu : 0 < nu)
    (hk0 : 0 ≤ kappa) (hk : kappa < alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ, 1 ≤ a → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), ((a : ℝ)/(h : ℝ))^kappa*
      ((((h : ℝ)/(a : ℝ))^alpha/(h : ℝ))*Real.exp (-d*((h : ℝ)/(a : ℝ))^alpha)+
        exceptionalEnvelope alpha v d nu h a)) ≤ C := by
  obtain ⟨B, hB, hb⟩ := left_ordinary_weighted_row_bound ha hk hd
  obtain ⟨D, hD, he⟩ := left_exceptional_weighted_row_bound ha hv hd hnu hk0
  refine ⟨B+D, add_pos hB hD, ?_⟩
  intro a ha1 M
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hs := add_le_add (hb (a : ℝ) haR M) (he a ha1 M)
  simpa only [mul_add, Finset.sum_add_distrib, mul_assoc, neg_mul] using hs

end Luce.Section6
