import Luce.Section6EarlyRateFloor
import Luce.Section6RateFloorLp

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The earliest actual gaps, including q=0, at an active left endpoint.
The complete rate-floor premise is derived from the original profile. -/
theorem PowerProfile.early_left_insertion_Lp {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r Q p0 : ℕ) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    q.val ≤ Q → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*((w n).rate i/(n : ℝ)^alpha)) := by
  obtain ⟨B, N, hB, hN, hb⟩ := hp.left_fixed_removal_rate_floor (r+Q)
  refine ⟨(2*(p0.factorial : ℝ))/B, N, by positivity, hN, ?_⟩
  intro grid w hw n hn hlarge removed hremoved i q p hq hpp hpp0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hW : 0 < B*(n : ℝ)^alpha := by positivity
  have hfloor : ∀ σ, B*(n : ℝ)^alpha ≤ orderedRemainingRate (compactDeletedWeights (w n) removed) σ q := by
    intro σ
    rw [← total_compl_deletedPrefixLabels]
    apply hb grid w hw n hn hlarge
    have hh := deletedPrefixLabels_card_le removed σ q
    omega
  have he := deleted_kernel_Lp_of_rate_floor (w n) removed i q p p0 hpp hpp0 hW hfloor
  convert he using 1 <;> congr 1 <;> ring

end Luce.Section6
