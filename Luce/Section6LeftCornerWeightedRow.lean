import Luce.Section6LeftEnvelopeWeightedSum
import Luce.Section6InsertionLpEnvelope
import Luce.Section6SampledWeightedSubsets

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Actual same-corner left weighted insertion rows, including exceptional
edges and every positive source depth in the derived source block. -/
theorem PowerProfile.left_corner_weighted_insertion_row {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta kappa : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hk0 : 0 ≤ kappa) (hk : kappa < alpha) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C H delta : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta ≤ 1/2 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n →
    ∀ (i : Fin n), ((i.val : ℝ)+1)/(n : ℝ) ≤ delta →
    ∀ (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n)) (q : Fin n → ℕ)
      (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, H ≤ ((j.val : ℝ)+1) ∧ ((j.val : ℝ)+1)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, d, nu, H, delta, hB, hd, hnu, hH, hdelta, hdelta1, hb⟩ :=
    hp.left_insertion_Lp_envelope r p0 hp0 1 zero_lt_one le_rfl
  have ha : 0 < alpha := zero_lt_one.trans hp.2.2.1.2.1
  obtain ⟨D, hD, hsum⟩ := left_envelope_weighted_sum_bound ha zero_lt_one hd hnu hk0 hk
  refine ⟨B*D, max H (8*(r : ℝ)+8), min (delta/2) (1/2), mul_pos hB hD,
    hH.trans_le (le_max_left _ _), lt_min (half_pos hdelta) (by norm_num), min_le_right _ _, ?_⟩
  intro grid w hw n hn i hismall s removed q p hpp hpp0 hs
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi0 : 0 < (i.val : ℝ)+1 := by positivity
  have hismall' : ((i.val : ℝ)+1)/(n : ℝ) < delta :=
    (hismall.trans (min_le_left _ _)).trans_lt (half_lt_self hdelta)
  let F : ℕ → ℝ := fun h => (((i.val : ℝ)+1)/(h : ℝ))^kappa*
    ((((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ))*
      Real.exp (-d*((h : ℝ)/((i.val : ℝ)+1))^alpha)+
      exceptionalEnvelope alpha 1 d nu h (i.val+1))
  have hF (h : ℕ) (hh : 1 ≤ h) : 0 ≤ F h := by
    dsimp [F]
    exact mul_nonneg (by positivity) (add_nonneg (by positivity) (exceptionalEnvelope_nonneg _ _ _ _ _ _))
  have hinj : Function.Injective (fun j : Fin n => j.val+1) := by
    intro a b hab
    dsimp at hab
    exact Fin.ext (by omega)
  have hfinite := positive_depth_subset_sum_le s (fun j => j.val+1) hinj
    (fun j => ⟨by omega, by omega⟩) F hF
  have hfinite' : (∑ j ∈ s, F (j.val+1)) ≤ D := by
    apply hfinite.trans
    simpa only [F, Nat.cast_add, Nat.cast_one] using hsum (i.val+1) (by omega) n
  calc
    _ ≤ ∑ j ∈ s, ENNReal.ofReal (B*F (j.val+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hjH, hjsmall, hremoved, hshift⟩ := hs j hj
      have hjH' : H ≤ ((j.val+1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using (le_max_left _ _).trans hjH
      have hjsmall' : ((j.val+1 : ℕ) : ℝ)/(n : ℝ) < delta := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (hjsmall.trans (min_le_left _ _)).trans_lt (half_lt_self hdelta)
      have hjrange : 8*r+8 ≤ j.val+1 := by
        have hh := (le_max_right _ _).trans hjH
        exact_mod_cast hh
      have hjhalf : 2*(j.val+1) ≤ n := by
        have hh := (div_le_iff₀ hnR).mp (hjsmall.trans (min_le_right _ _))
        have hh' : 2*((j.val : ℝ)+1) ≤ n := by linarith
        exact_mod_cast hh'
      have hcard : (Finset.univ \ removed j).card = n-(removed j).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have hq : q j < (Finset.univ \ removed j).card := by
        rw [hcard]
        exact shifted_left_nonterminal hremoved hjrange hjhalf (by simpa using hshift)
      have he := hb grid w hw n (j.val+1) hn hjH' hjsmall' (removed j) hremoved
        i hismall' ⟨q j, hq⟩ p hpp hpp0 (by simpa using hshift)
      have hweight : 0 ≤ (((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa := by positivity
      have hm := mul_le_mul_of_nonneg_left he
        (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa) from zero_le)
      rw [← ENNReal.ofReal_mul hweight] at hm
      simpa only [F, exceptionalEnvelope, Nat.cast_add, Nat.cast_one, min_comm, mul_assoc, mul_left_comm] using hm
    _ = ENNReal.ofReal (B*(∑ j ∈ s, F (j.val+1))) := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg hB.le (hF _ (by omega)))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hfinite' hB.le)

end Luce.Section6
