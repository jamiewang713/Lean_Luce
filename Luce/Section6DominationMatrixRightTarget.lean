import Luce.Section6DominationMatrixSmallRows
import Luce.Section6CornerInsertionTarget
import Luce.Section6RightOutsideTarget
import Luce.Section6GapOffsets

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Active right-endpoint target maxima for the same concrete matrix, every
source and every row size, including fixed terminal depths. -/
theorem PowerProfile.domination_matrix_right_target {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ i j : Fin n, (terminalDepth j : ℝ)/(n : ℝ) ≤ delta →
      insertionDominationMatrix (w n) r p i j ≤ C/(terminalDepth j : ℝ) := by
  obtain ⟨B, H, sigma, hB, hH, hsigma, hsigma1, hb⟩ :=
    hp.right_corner_insertion_target_bound r p hp1
  obtain ⟨D, K, delta, N, hD, hK, hd, hd1, hN, he⟩ :=
    hp.right_outside_insertion_target_bound hsigma hsigma1 r p hp1
  let T : ℝ := max H (max K (8*(r : ℝ)+8))
  let C : ℝ := B+D+T+N
  have hT : 0 < T := hH.trans_le (le_max_left _ _)
  have hC : 0 < C := by dsimp [C]; positivity
  have hmin : 0 < min sigma delta := lt_min hsigma hd
  refine ⟨C, min sigma delta/2, hC, half_pos hmin,
    (half_lt_self hmin).trans ((min_le_right _ _).trans_lt hd1), ?_⟩
  intro grid w hw n i j hsmall
  have hsmall' : (terminalDepth j : ℝ)/(n : ℝ) < min sigma delta :=
    hsmall.trans_lt (half_lt_self hmin)
  have hn : 0 < n := by have := j.isLt; omega
  have hh : 0 < (terminalDepth j : ℝ) := Nat.cast_pos.mpr (terminalDepth_pos j)
  have hhn : terminalDepth j ≤ n := by unfold terminalDepth; omega
  have hhnR : (terminalDepth j : ℝ) ≤ n := by exact_mod_cast hhn
  have hCB : B ≤ C := by dsimp [C]; linarith
  have hCD : D ≤ C := by dsimp [C]; linarith
  have hCT : T ≤ C := by dsimp [C]; linarith
  have hCN : N ≤ C := by dsimp [C]; linarith
  by_cases hlarge : N ≤ (n : ℝ)
  · by_cases hdepth : T ≤ (terminalDepth j : ℝ)
    · obtain ⟨removed, q, hremoved, hshift, hval⟩ :=
        insertionDominationMatrix_attained (w n) r p i j
      have hgap : Nat.dist q (n-terminalDepth j) ≤ r+1 := by
        have hj : n-terminalDepth j = j.val := by unfold terminalDepth; omega
        rwa [hj]
      have hbuffer : 8*r+8 ≤ terminalDepth j := by
        have hhR := (le_max_right H _).trans hdepth
        have hhR' := (le_max_right K (8*(r : ℝ)+8)).trans hhR
        exact_mod_cast hhR'
      have hcard : (Finset.univ \ removed).card = n-removed.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have hq : q < (Finset.univ \ removed).card := by
        rw [hcard]
        exact (shifted_right_survivor_bounds hremoved hhn hbuffer hgap).1
      apply (ENNReal.ofReal_le_ofReal_iff (div_pos hC hh).le).mp
      rw [hval]
      by_cases hi : (terminalDepth i : ℝ)/(n : ℝ) < sigma
      · exact (hb grid w hw n (terminalDepth j) hn ((le_max_left _ _).trans hdepth)
          (hsmall'.trans_le (min_le_left _ _)) removed hremoved i hi ⟨q, hq⟩ p hp1 le_rfl hgap).trans
          (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hCB hh.le))
      · exact (he grid w hw n (terminalDepth j) hn hlarge
          ((le_max_left K _).trans ((le_max_right H _).trans hdepth)) hbuffer
          (hsmall'.trans_le (min_le_right _ _)) removed hremoved i (le_of_not_gt hi)
          ⟨q, hq⟩ p hp1 le_rfl hgap).trans
          (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hCD hh.le))
    · apply (insertionDominationMatrix_le_one (w n) r p i j).trans
      exact (le_div_iff₀ hh).mpr (by simpa using (le_of_not_ge hdepth).trans hCT)
  · apply (insertionDominationMatrix_le_one (w n) r p i j).trans
    exact (le_div_iff₀ hh).mpr (by simpa using hhnR.trans ((le_of_not_ge hlarge).trans hCN))

end Luce.Section6
