import Luce.Section6LeftCornerAllTargets
import Luce.Section6OutsideLeftAllWeightedRow

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Complete left-endpoint weighted insertion contribution for all source
labels and every positive target depth in a derived endpoint block. -/
theorem PowerProfile.left_endpoint_weighted_insertion_row {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta kappa : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hk0 : 0 ≤ kappa) (hk : kappa < alpha) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C delta N : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1/2 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, ((j.val : ℝ)+1)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, delta, N, hB, hd, hdh, hN, hb⟩ :=
    hp.left_corner_all_targets_weighted_row hk0 hk r p0 hp0
  have hd1 : delta < 1 := hdh.trans_lt (by norm_num)
  obtain ⟨D, eps, M, hD, heps, hepsd, hepsh, hM, he⟩ :=
    hp.outside_left_all_weighted_row hd hd1 hk0 hk r p0
  refine ⟨B+D, min delta eps, max N M, add_pos hB hD, lt_min hd heps,
    (min_le_left _ _).trans hdh, hN.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n hn hlarge i s removed q p hpp hpp0 hs
  by_cases hi : ((i.val : ℝ)+1)/(n : ℝ) ≤ delta
  · have hrow := hb grid w hw n hn ((le_max_left _ _).trans hlarge) i hi s removed q p hpp hpp0
      (fun j hj => ⟨((hs j hj).1).trans (min_le_left _ _), (hs j hj).2⟩)
    exact hrow.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · have hrow := he grid w hw n hn ((le_max_right _ _).trans hlarge) i s removed q p
      (le_of_lt (lt_of_not_ge hi)) hpp hpp0
      (fun j hj => ⟨((hs j hj).1).trans (min_le_right _ _), (hs j hj).2⟩)
    exact hrow.trans (ENNReal.ofReal_le_ofReal (by linarith))

end Luce.Section6
