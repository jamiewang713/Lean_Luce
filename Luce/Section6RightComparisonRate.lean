import Luce.Section6RightRealDepthMean
import Luce.Section6SurvivorMeanTail
import Luce.Section6SurvivalEnvelope

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- The right survival estimate at any larger real comparison depth y.
The actual source rate is retained for outside-block estimates. -/
theorem PowerProfile.right_comparison_depth_survival_rate {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r : ℕ) :
    ∃ d H delta : ℝ, 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n h : ℕ) (y : ℝ), 0 < n → H ≤ y → 8*r+8 ≤ h →
    (h : ℝ) ≤ y → y/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p →
    Nat.dist q.val (n-h) ≤ r+1 →
    (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*raceGapStart (compactDeletedClocks removed old) q))
      ∂exponentialRace (w n)) ≤
      Real.exp (-d*((w n).rate i*((n : ℝ)/y)^beta))+Real.exp (-d*y) := by
  obtain ⟨k, H, delta, hk, hk1, hH, hd, hd1, hmean⟩ := hp.right_early_deleted_mean_real_depth r
  have hrho : 0 < 8*bernoulliLowerTailConstant := by positivity [bernoulliLowerTailConstant_pos]
  refine ⟨min k (8*bernoulliLowerTailConstant), H, delta,
    lt_min hk hrho, hH, hd, hd1, ?_⟩
  intro grid w hw n h y hn hhH hh hhy hsmall removed hremoved i q p hpp hshift
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hy : 0 < y := hH.trans_le hhH
  have hhn : h ≤ n := by
    have := (div_lt_one hnR).mp (hsmall.trans hd1)
    exact Nat.le_of_lt (Nat.cast_lt.mp (hhy.trans_lt this))
  obtain ⟨hq, hlower, hupper⟩ := shifted_right_survivor_bounds hremoved hhn hh hshift
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hR : ((Finset.univ \ removed).card : ℝ)-(q.val : ℝ) = ((n-removed.card-q.val : ℕ) : ℝ) := by
    rw [Nat.cast_sub hq.le]
    exact congrArg (fun x : ℕ => (x : ℝ)-(q.val : ℝ)) hcard
  have huR : ((Finset.univ \ removed).card : ℝ)-(q.val : ℝ) ≤ 2*(h : ℝ) := by
    rw [hR]
    exact_mod_cast hupper
  let t := k*((n : ℝ)/y)^beta
  have ht : 0 < t := mul_pos hk (Real.rpow_pos_of_pos (div_pos hnR hy) _)
  have hm := hmean grid w hw n y hn hy hhH hsmall removed hremoved
  have hthreshold : 2*(((Finset.univ \ removed).card : ℝ)-(q.val : ℝ)) ≤
      (n : ℝ)*deletedH (w n) removed t := by dsimp [t]; nlinarith
  have htail : (exponentialRace (w n)).real {old |
      raceGapStart (compactDeletedClocks removed old) q < t} ≤
      Real.exp (-(8*bernoulliLowerTailConstant)*y) := by
    apply (deleted_gap_start_tail_of_survivor_mean_sharp (w n) hn removed q ht.le hthreshold).trans
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hm bernoulliLowerTailConstant_pos.le
    dsimp [t]
    nlinarith
  have hi := (w n).positive i
  have hrate : k*((w n).rate i*((n : ℝ)/y)^beta) ≤ (w n).rate i*t := by
    dsimp [t]
    exact le_of_eq (by ring)
  exact deleted_survival_envelope_of_bounds (w n) removed i q p hpp
    (by positivity) hy.le hk.le (min_le_left _ _) (min_le_right _ _) hrate htail

end Luce.Section6
