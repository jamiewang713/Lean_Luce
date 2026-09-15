import Luce.Section6EarlyRateLp
import Luce.Section6InactiveBounds

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Actual demanded-rank shifts in the initial eighth, including the first
gap. Nonterminal membership and the rate-floor range are proved internally. -/
theorem PowerProfile.early_shifted_rate_Lp {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right) (p0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 8*r+8 ≤ n → 1 ≤ h → 8*h ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q p : ℕ), Nat.dist q (h-1) ≤ r+1 → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (C*(w n).rate i/(n : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := hp.early_insertion_rate_Lp p0
  refine ⟨C, hC, ?_⟩
  intro grid w hw n r h hn hh hregion removed hremoved i q p hshift hpp hpp0
  have hcard : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hq : q < (Finset.univ \ removed).card := by
    unfold Nat.dist at hshift
    omega
  have hq4 : 4*q ≤ n := by unfold Nat.dist at hshift; omega
  exact hb grid w hw n r (by omega) removed hremoved i ⟨q, hq⟩ p hq4 hpp hpp0

/-- The inactive-left C/n consequence, now including all bounded shifts in
the early target region. Its uniform source-rate bound is derived. -/
theorem PowerProfile.inactive_left_shifted_Lp {f : ℝ → ℝ}
    {right : EndpointBehavior} {c : ℝ} (hp : PowerProfile f (.finite c) right) (p0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 8*r+8 ≤ n → 1 ≤ h → 8*h ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q p : ℕ), Nat.dist q (h-1) ≤ r+1 → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (C/(n : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := hp.early_shifted_rate_Lp p0
  obtain ⟨M, hM, hupper⟩ := hp.global_upper_of_left_finite
  refine ⟨B*M, mul_pos hB hM, ?_⟩
  intro grid w hw n r h hn hh hregion removed hremoved i q p hshift hpp hpp0
  apply (hb grid w hw n r h hn hh hregion removed hremoved i q p hshift hpp hpp0).trans
  apply ENNReal.ofReal_le_ofReal
  have hi : (w n).rate i ≤ M := by rw [hw n i]; exact hupper _ (samplePoint_mem grid i)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi hB.le) (Nat.cast_nonneg n)

end Luce.Section6
