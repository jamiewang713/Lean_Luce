import Luce.Section6RightEnvelopeWeightedSum
import Luce.Section6InsertionLpEnvelope
import Luce.Section6SampledWeightedSubsets

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Actual right-corner weighted insertion rows for moderate target depths,
including exceptional edges and every positive source depth in the block. -/
theorem PowerProfile.right_corner_weighted_insertion_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk0 : 0 ≤ kappa) (hk : kappa < beta) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C H delta : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta ≤ 1/2 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n →
    ∀ (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) ≤ delta →
    ∀ (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n)) (q : Fin n → ℕ)
      (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, H ≤ (terminalDepth j : ℝ) ∧ (terminalDepth j : ℝ)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, d, nu, H, delta, hB, hd, hnu, hH, hdelta, hdelta1, hb⟩ :=
    hp.right_insertion_Lp_envelope r p0 hp0 1 zero_lt_one le_rfl
  have hbeta : 0 < beta := hp.2.2.2.1.2.1
  obtain ⟨D, hD, hsum⟩ := right_envelope_weighted_sum_bound hbeta zero_lt_one hd hnu hk0 hk
  refine ⟨B*D, max H (8*(r : ℝ)+8), min (delta/2) (1/2), mul_pos hB hD,
    hH.trans_le (le_max_left _ _), lt_min (half_pos hdelta) (by norm_num), min_le_right _ _, ?_⟩
  intro grid w hw n hn i hismall s removed q p hpp hpp0 hs
  have hismall' : (terminalDepth i : ℝ)/(n : ℝ) < delta :=
    (hismall.trans (min_le_left _ _)).trans_lt (half_lt_self hdelta)
  let F : ℕ → ℝ := fun h => ((h : ℝ)/(terminalDepth i : ℝ))^kappa*
    ((((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ))*
      Real.exp (-d*((terminalDepth i : ℝ)/(h : ℝ))^beta)+
      exceptionalEnvelope beta 1 d nu (terminalDepth i) h)
  have hF (h : ℕ) (hh : 1 ≤ h) : 0 ≤ F h := by
    dsimp [F]
    exact mul_nonneg (by positivity) (add_nonneg (by positivity) (exceptionalEnvelope_nonneg _ _ _ _ _ _))
  have hinj : Function.Injective (terminalDepth : Fin n → ℕ) := by
    intro a b hab
    apply Fin.ext
    unfold terminalDepth at hab
    have ha := a.isLt
    have hb := b.isLt
    omega
  have hfinite := positive_depth_subset_sum_le s terminalDepth hinj
    (fun j => ⟨terminalDepth_pos j, Nat.sub_le _ _⟩) F hF
  have hfinite' : (∑ j ∈ s, F (terminalDepth j)) ≤ D :=
    hfinite.trans (hsum (terminalDepth i) (terminalDepth_pos i) n)
  calc
    _ ≤ ∑ j ∈ s, ENNReal.ofReal (B*F (terminalDepth j)) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hjH, hjsmall, hremoved, hshift⟩ := hs j hj
      have hjH' : H ≤ (terminalDepth j : ℝ) := (le_max_left _ _).trans hjH
      have hjsmall' : (terminalDepth j : ℝ)/(n : ℝ) < delta :=
        (hjsmall.trans (min_le_left _ _)).trans_lt (half_lt_self hdelta)
      have hjrange : 8*r+8 ≤ terminalDepth j := by
        have hh := (le_max_right _ _).trans hjH
        exact_mod_cast hh
      have hjrank : n-terminalDepth j = j.val := by
        unfold terminalDepth
        omega
      have hcard : (Finset.univ \ removed j).card = n-(removed j).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have hq : q j < (Finset.univ \ removed j).card := by
        rw [hcard]
        exact (shifted_right_survivor_bounds hremoved (Nat.sub_le _ _) hjrange
          (by change Nat.dist (q j) (n-terminalDepth j) ≤ r+1; rwa [hjrank])).1
      have he := hb grid w hw n (terminalDepth j) hn hjH' hjsmall' (removed j) hremoved
        i hismall' ⟨q j, hq⟩ p hpp hpp0 (by simpa only [hjrank] using hshift)
      have hweight : 0 ≤ ((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa := by positivity
      have hm := mul_le_mul_of_nonneg_left he
        (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa) from zero_le)
      rw [← ENNReal.ofReal_mul hweight] at hm
      simpa only [F, exceptionalEnvelope, mul_assoc, mul_left_comm] using hm
    _ = ENNReal.ofReal (B*(∑ j ∈ s, F (terminalDepth j))) := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg
        (fun j _ => mul_nonneg hB.le (hF _ (terminalDepth_pos j)))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hfinite' hB.le)

end Luce.Section6
