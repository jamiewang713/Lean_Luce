import Luce.Section6LogarithmicReservoir
import Luce.Section6SurvivorMeanTail
import Luce.Section6GapOffsets

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- The logarithmic order-time tail from the actual interior survivor
reservoir. No endpoint lower bound is required for this probability bound. -/
theorem logarithmic_gap_start_tail {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 1)) (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x) :
    ∃ c rho : ℝ, 0 < c ∧ 0 < rho ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 8 ≤ n → 16*r ≤ n → 8*r+8 ≤ h → 16384*h ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ q : Fin (Finset.univ \ removed).card, Nat.dist q.val (n-h) ≤ r+1 →
    (exponentialRace (w n)).real {old | raceGapStart (compactDeletedClocks removed old) q <
      c*Real.log ((n : ℝ)/(h : ℝ))} ≤
      Real.exp (-rho*Real.sqrt ((n : ℝ)*(h : ℝ))) := by
  obtain ⟨c, M, hc, hM, hMc, hm⟩ := interior_logarithmic_survivor_mean hf hpos
  refine ⟨c, bernoulliLowerTailConstant/16, hc, by positivity [bernoulliLowerTailConstant_pos], ?_⟩
  intro grid w hw n r h hn hr hh hsmall removed hremoved q hshift
  have hn0 : 0 < n := by omega
  have hh0 : 0 < h := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh0
  have hhn : h ≤ n := by omega
  have hhnR : (h : ℝ) ≤ n := by exact_mod_cast hhn
  have hl : 0 ≤ Real.log ((n : ℝ)/(h : ℝ)) := Real.log_nonneg ((one_le_div hhR).mpr hhnR)
  have ht : 0 ≤ c*Real.log ((n : ℝ)/(h : ℝ)) := mul_nonneg hc.le hl
  obtain ⟨hq, _, hupper⟩ := shifted_right_survivor_bounds hremoved hhn hh hshift
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hR : ((Finset.univ \ removed).card : ℝ)-(q.val : ℝ) = ((n-removed.card-q.val : ℕ) : ℝ) := by
    rw [Nat.cast_sub hq.le]
    exact congrArg (fun x : ℕ => (x : ℝ)-(q.val : ℝ)) hcard
  have hu : ((Finset.univ \ removed).card : ℝ)-(q.val : ℝ) ≤ 2*(h : ℝ) := by
    rw [hR]
    exact_mod_cast hupper
  have hsmallR : 16384*(h : ℝ) ≤ n := by exact_mod_cast hsmall
  have hsqrt : 128*(h : ℝ) ≤ Real.sqrt ((n : ℝ)*(h : ℝ)) := by
    have hs := Real.sq_sqrt (mul_nonneg hnR.le hhR.le)
    have hp := mul_le_mul_of_nonneg_right hsmallR hhR.le
    nlinarith [Real.sqrt_nonneg ((n : ℝ)*(h : ℝ))]
  have hmean := hm grid w hw n r hn hr removed hremoved (h : ℝ) hhR hhnR
  have hthreshold : 2*(((Finset.univ \ removed).card : ℝ)-(q.val : ℝ)) ≤
      (n : ℝ)*deletedH (w n) removed (c*Real.log ((n : ℝ)/(h : ℝ))) := by linarith
  apply (deleted_gap_start_tail_of_survivor_mean_sharp (w n) hn0 removed q ht hthreshold).trans
  apply Real.exp_le_exp.mpr
  have he := mul_le_mul_of_nonneg_left hmean bernoulliLowerTailConstant_pos.le
  nlinarith only [he]

end Luce.Section6
