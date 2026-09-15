import Luce.Section6RightTailMean
import Luce.Section6SurvivorConcentration
import Luce.Section6GapOffsets

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- The right endpoint order-statistic lower tail on the original deleted
race, with the numerical survivor-mean premise completely discharged. -/
theorem PowerProfile.right_gap_start_lower_tail {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r : ℕ) :
    ∃ k H delta rho : ℝ, 0 < k ∧ k ≤ 1 ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧ 0 < rho ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ q : Fin (Finset.univ \ removed).card, Nat.dist q.val (n-h) ≤ r+1 →
    (exponentialRace (w n)).real {old |
      raceGapStart (compactDeletedClocks removed old) q < k*((n : ℝ)/(h : ℝ))^beta} ≤
      Real.exp (-rho*(h : ℝ)) := by
  obtain ⟨k, H, delta, hk, hk1, hH, hd, hd1, hmean⟩ := hp.right_early_deleted_mean r
  refine ⟨k, H, delta, bernoulliLowerTailConstant, hk, hk1, hH, hd, hd1,
    bernoulliLowerTailConstant_pos, ?_⟩
  intro grid w hw n h hn hhH hh hsmall removed hremoved q hshift
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhpos : 0 < h := by omega
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hhpos
  have hle : h ≤ n := Nat.le_of_lt (Nat.cast_lt.mp ((div_lt_one hnR).mp (hsmall.trans hd1)))
  obtain ⟨hq, hlower, hupper⟩ := shifted_right_survivor_bounds hremoved hle hh hshift
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hR : ((Finset.univ \ removed).card : ℝ)-(q.val : ℝ) = ((n-removed.card-q.val : ℕ) : ℝ) := by
    rw [Nat.cast_sub hq.le]
    exact congrArg (fun x : ℕ => (x : ℝ)-(q.val : ℝ)) hcard
  have hlR : (h : ℝ) ≤ 2*(((Finset.univ \ removed).card : ℝ)-(q.val : ℝ)) := by
    rw [hR]
    exact_mod_cast hlower
  have huR : ((Finset.univ \ removed).card : ℝ)-(q.val : ℝ) ≤ 2*(h : ℝ) := by
    rw [hR]
    exact_mod_cast hupper
  have ht : 0 < k*((n : ℝ)/(h : ℝ))^beta :=
    mul_pos hk (Real.rpow_pos_of_pos (div_pos hnR hhR) _)
  have hm : 2*(((Finset.univ \ removed).card : ℝ)-(q.val : ℝ)) ≤
      (n : ℝ)*deletedH (w n) removed (k*((n : ℝ)/(h : ℝ))^beta) :=
    le_trans (by nlinarith) (hmean grid w hw n h hn hhpos hhH hsmall removed hremoved)
  apply (deleted_gap_start_tail_of_survivor_mean (w n) hn removed q ht.le hm).trans
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hlR bernoulliLowerTailConstant_pos.le]

end Luce.Section6
