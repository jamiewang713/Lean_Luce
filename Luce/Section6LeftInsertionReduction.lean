import Luce.Section6InsertionRatio
import Luce.Section6LeftInsertionMoment

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- The left insertion moment with x_L(a,h)/h, at the actual nonfinal gap
index h=q. Finite deletion/rank conditions are those of the proved floor. -/
theorem PowerProfile.left_insertion_moment_reduction {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ B delta eps : ℝ, 0 < B ∧ 0 < delta ∧ delta < 1 ∧ 0 < eps ∧ eps < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 0 < n → ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    4*r+4 ≤ q.val → (q.val : ℝ) ≤ eps*(n : ℝ)/4 →
    ((i.val : ℝ)+1)/(n : ℝ) < delta →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*(B*(((q.val : ℝ)/((i.val : ℝ)+1))^alpha/(q.val : ℝ)))^p*
      (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*
        raceGapStart (compactDeletedClocks removed old) q)) ∂exponentialRace (w n)) := by
  obtain ⟨C, eps, hC, heps, heps1, hmoment⟩ := hp.left_deleted_insertion_moment
  obtain ⟨K, delta, hK, hd, hd1, hrate⟩ := hp.left_sampled_rate_upper
  refine ⟨K/C, delta, eps, div_pos hK hC, hd, hd1, heps, heps1, ?_⟩
  intro grid w hw n r hn removed hremoved i q p hq hqn hi
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < q.val := Nat.cast_pos.mpr (by omega)
  have haR : 0 < (i.val : ℝ)+1 := by positivity
  have hden : 0 < C*(n : ℝ)^alpha*(q.val : ℝ)^(1-alpha) :=
    mul_pos (mul_pos hC (Real.rpow_pos_of_pos hnR _)) (Real.rpow_pos_of_pos hhR _)
  have hr := div_le_div_of_nonneg_right (hrate grid w hw n i hi) hden.le
  rw [left_insertion_ratio_identity hC hnR haR hhR] at hr
  apply (hmoment grid w hw n r hn removed hremoved i q p hq hqn).trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_left₀ (div_nonneg ((w n).positive i).le hden.le) hr p
    · positivity
  · exact integral_nonneg (fun _ => (Real.exp_pos _).le)

end Luce.Section6
