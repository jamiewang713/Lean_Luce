import Luce.Section6InsertionRatio
import Luce.Section6RightInsertionMoment

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- The right insertion moment has the manuscript x_R(a,h)/h factor.
The exact survival expectation is retained; concentration is a later obligation. -/
theorem PowerProfile.right_insertion_moment_reduction {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ B delta : ℝ, 0 < B ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ (removed : Finset (Fin n)) (i : Fin n)
      (q : Fin (Finset.univ \ removed).card) (h p : ℕ),
    0 < h → h+removed.card+q.val ≤ n → (terminalDepth i : ℝ)/(n : ℝ) < delta →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*(B*(((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ)))^p*
      (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*
        raceGapStart (compactDeletedClocks removed old) q)) ∂exponentialRace (w n)) := by
  obtain ⟨C, hC, hmoment⟩ := hp.right_deleted_insertion_moment
  obtain ⟨K, delta, hK, hd, hd1, hrate⟩ := hp.right_sampled_rate_upper
  refine ⟨K/C, delta, div_pos hK hC, hd, hd1, ?_⟩
  intro grid w hw n hn removed i q h p hh hcount hi
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have haR : (0 : ℝ) < terminalDepth i := Nat.cast_pos.mpr (terminalDepth_pos i)
  have hden : 0 < C*(n : ℝ)^(-beta)*(h : ℝ)^(beta+1) :=
    mul_pos (mul_pos hC (Real.rpow_pos_of_pos hnR _)) (Real.rpow_pos_of_pos hhR _)
  have hr := div_le_div_of_nonneg_right (hrate grid w hw n i hi) hden.le
  rw [right_insertion_ratio_identity hC hnR haR hhR] at hr
  apply (hmoment grid w hw n hn removed i q h p hh hcount).trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_left₀ (div_nonneg ((w n).positive i).le hden.le) hr p
    · positivity
  · exact integral_nonneg (fun _ => (Real.exp_pos _).le)

end Luce.Section6
