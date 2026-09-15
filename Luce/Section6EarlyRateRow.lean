import Luce.Section6EarlyShiftedRateLp

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- The total early-target insertion norm retains O(theta_i), including
when the deletion set and gap shift vary with the target label. -/
theorem PowerProfile.early_insertion_rate_row {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right) (p0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 8*r+8 ≤ n →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, 8*(j.val+1) ≤ n ∧ (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal (C*(w n).rate i) := by
  obtain ⟨C, hC, hb⟩ := hp.early_shifted_rate_Lp p0
  refine ⟨C, hC, ?_⟩
  intro grid w hw n r hn i s removed q p hpp hpp0 hs
  have hi := (w n).positive i
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hterm : 0 ≤ C*(w n).rate i/(n : ℝ) := by positivity
  calc
    _ ≤ ∑ _j ∈ s, ENNReal.ofReal (C*(w n).rate i/(n : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hrange, hremoved, hshift⟩ := hs j hj
      exact hb grid w hw n r (j.val+1) hn (by omega) hrange (removed j) hremoved
        i (q j) p (by simpa using hshift) hpp hpp0
    _ = ENNReal.ofReal (∑ _j ∈ s, C*(w n).rate i/(n : ℝ)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ => hterm)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hc : (s.card : ℝ) ≤ n := by
        have hcN : s.card ≤ n := by simpa using s.card_le_univ
        exact_mod_cast hcN
      simp only [Finset.sum_const, nsmul_eq_mul]
      calc
        _ ≤ (n : ℝ)*(C*(w n).rate i/(n : ℝ)) := mul_le_mul_of_nonneg_right hc hterm
        _ = _ := by field_simp

end Luce.Section6
