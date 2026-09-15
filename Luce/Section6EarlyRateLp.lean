import Luce.Section6InteriorRemainingRate
import Luce.Section6RateFloorLp

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Initial-quarter insertion norms retaining the actual source rate, as
needed for the weighted row estimate. No endpoint is required inactive. -/
theorem PowerProfile.early_insertion_rate_Lp {f : ℝ → ℝ}
    {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (p0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 4*r+4 ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    4*q.val ≤ n → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (C*(w n).rate i/(n : ℝ)) := by
  obtain ⟨B, hB, hfloor⟩ := hp.interior_remaining_rate (eps := 1/2) (by norm_num)
  refine ⟨(2*(p0.factorial : ℝ))/B, by positivity, ?_⟩
  intro grid w hw n r hn removed hremoved i q p hq hpp hpp0
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hW : 0 < B*(n : ℝ) := mul_pos hB hnR
  have hf : ∀ σ, B*(n : ℝ) ≤ orderedRemainingRate (compactDeletedWeights (w n) removed) σ q := by
    intro σ
    rw [← total_compl_deletedPrefixLabels]
    apply hfloor grid w hw n hn0
    have hh := deletedPrefixLabels_card_le removed σ q
    have hc : n ≤ 2*(Finset.univ \ deletedPrefixLabels removed σ q).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    have hcR : (n : ℝ) ≤ 2*((Finset.univ \ deletedPrefixLabels removed σ q).card : ℝ) := by exact_mod_cast hc
    linarith
  have hb := deleted_kernel_Lp_of_rate_floor (w n) removed i q p p0 hpp hpp0 hW hf
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hb

end Luce.Section6
