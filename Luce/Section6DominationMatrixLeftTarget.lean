import Luce.Section6DominationMatrixSmallRows
import Luce.Section6CornerInsertionTarget
import Luce.Section6LeftOutsideTarget
import Luce.Section6GapOffsets

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Active left-endpoint target maxima, including every source, row size
and fixed initial depth, for the existing concrete domination matrix. -/
theorem PowerProfile.domination_matrix_left_target {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ i j : Fin n, ((j.val : ℝ)+1)/(n : ℝ) ≤ delta →
      insertionDominationMatrix (w n) r p i j ≤ C/((j.val : ℝ)+1) := by
  obtain ⟨B, H, sigma, hB, hH, hsigma, hsigma1, hb⟩ :=
    hp.left_corner_insertion_target_bound r p hp1
  obtain ⟨D, delta, hD, hd, hds, he⟩ :=
    hp.left_outside_insertion_target_bound hsigma hsigma1 p
  let T : ℝ := max H (8*(r : ℝ)+8)
  let C : ℝ := B+D+T
  let eps : ℝ := min sigma (min delta 1)
  have heps : 0 < eps := lt_min hsigma (lt_min hd zero_lt_one)
  have hT : 0 < T := hH.trans_le (le_max_left _ _)
  have hC : 0 < C := by dsimp [C]; positivity
  have heps1 : eps ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C, eps/2, hC, half_pos heps, by linarith, ?_⟩
  intro grid w hw n i j hsmall
  have hn : 0 < n := by have := j.isLt; omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh : 0 < (j.val : ℝ)+1 := by positivity
  have hhnR : (j.val : ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt j.isLt)
  have hhalf : ((j.val : ℝ)+1)/(n : ℝ) ≤ 1/2 := hsmall.trans (by linarith)
  have htwice : 2*(j.val+1) ≤ n := by
    have ht := (div_le_iff₀ hnR).mp hhalf
    have ht' : 2*((j.val : ℝ)+1) ≤ n := by linarith
    exact_mod_cast ht'
  have hsmall' : ((j.val : ℝ)+1)/(n : ℝ) < eps := hsmall.trans_lt (half_lt_self heps)
  have hCB : B ≤ C := by dsimp [C]; linarith
  have hCD : D ≤ C := by dsimp [C]; linarith
  have hCT : T ≤ C := by dsimp [C]; linarith
  by_cases hdepth : T ≤ (j.val : ℝ)+1
  · obtain ⟨removed, q, hremoved, hshift, hval⟩ :=
      insertionDominationMatrix_attained (w n) r p i j
    have hgap : Nat.dist q (j.val+1-1) ≤ r+1 := by simpa using hshift
    have hbuffer : 8*r+8 ≤ j.val+1 := by
      have ht := (le_max_right H (8*(r : ℝ)+8)).trans hdepth
      exact_mod_cast ht
    have hcard : (Finset.univ \ removed).card = n-removed.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have hq : q < (Finset.univ \ removed).card := by
      rw [hcard]
      exact shifted_left_nonterminal hremoved hbuffer htwice hgap
    apply (ENNReal.ofReal_le_ofReal_iff (div_pos hC hh).le).mp
    rw [hval]
    by_cases hi : ((i.val : ℝ)+1)/(n : ℝ) < sigma
    · have ht := hb grid w hw n (j.val+1) hn
        (by simpa using (le_max_left H _).trans hdepth)
        (by simpa using hsmall'.trans_le (min_le_left sigma _))
        removed hremoved i hi ⟨q, hq⟩ p hp1 le_rfl hgap
      exact ht.trans (ENNReal.ofReal_le_ofReal (by
        simpa using div_le_div_of_nonneg_right hCB hh.le))
    · have ht := he grid w hw n r (j.val+1) hn hbuffer
        (by simpa using hsmall'.le.trans ((min_le_right sigma _).trans (min_le_left delta 1)))
        removed hremoved i ⟨q, hq⟩ p hgap (le_of_not_gt hi) hp1 le_rfl
      exact ht.trans (ENNReal.ofReal_le_ofReal
        ((div_le_div_of_nonneg_left hD.le hh hhnR).trans
          (div_le_div_of_nonneg_right hCD hh.le)))
  · apply (insertionDominationMatrix_le_one (w n) r p i j).trans
    exact (le_div_iff₀ hh).mpr (by simpa using (le_of_not_ge hdepth).trans hCT)

end Luce.Section6
