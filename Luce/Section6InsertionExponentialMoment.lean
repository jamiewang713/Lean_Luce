import Luce.Section6SurvivalEnvelope
import Luce.Section6ShiftedInsertionMoment

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Actual insertion moments with the survival expectation eliminated using
only the original sampled-profile assumptions. The extreme-regime refinement
and conversion to the manuscript's Lp envelope remain separate obligations. -/
theorem PowerProfile.left_insertion_exponential_moment {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r : ℕ) :
    ∃ B d H delta : ℝ, 0 < B ∧ 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n), ((i.val : ℝ)+1)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p →
    Nat.dist q.val (h-1) ≤ r+1 →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*(B*(((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ)))^p*
        (Real.exp (-d*((h : ℝ)/((i.val : ℝ)+1))^alpha)+Real.exp (-d*(h : ℝ))) := by
  obtain ⟨B, dm, hB, hdm, hdm1, hmoment⟩ := hp.left_shifted_insertion_moment
  obtain ⟨d, H, ds, hd, hH, hds, hds1, hsurvival⟩ := hp.left_survival_envelope
  refine ⟨B, d, H, min dm ds, hB, hd, hH, lt_min hdm hds,
    (min_le_left _ _).trans_lt hdm1, ?_⟩
  intro grid w hw n h hn hhH hh hsmall removed hremoved i hi q p hpp hshift
  have hhm := hsmall.trans_le (min_le_left dm ds)
  have hhs := hsmall.trans_le (min_le_right dm ds)
  have him := hi.trans_le (min_le_left dm ds)
  have his := hi.trans_le (min_le_right dm ds)
  apply (hmoment grid w hw n r hn removed hremoved i q h p hh hhm him hshift).trans
  exact mul_le_mul_of_nonneg_left
    (hsurvival grid w hw n r h hn hhH hh hhs removed i his q p hpp hshift) (by positivity)

/-- Actual insertion moments with the survival expectation eliminated using
only the original sampled-profile assumptions. The extreme-regime refinement
and conversion to the manuscript's Lp envelope remain separate obligations. -/
theorem PowerProfile.right_insertion_exponential_moment {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r : ℕ) :
    ∃ B d H delta : ℝ, 0 < B ∧ 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p →
    Nat.dist q.val (n-h) ≤ r+1 →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*(B*(((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ)))^p*
        (Real.exp (-d*((terminalDepth i : ℝ)/(h : ℝ))^beta)+Real.exp (-d*(h : ℝ))) := by
  obtain ⟨B, dm, hB, hdm, hdm1, hmoment⟩ := hp.right_shifted_insertion_moment
  obtain ⟨d, H, ds, hd, hH, hds, hds1, hsurvival⟩ := hp.right_survival_envelope r
  refine ⟨B, d, H, min dm ds, hB, hd, hH, lt_min hdm hds,
    (min_le_left _ _).trans_lt hdm1, ?_⟩
  intro grid w hw n h hn hhH hh hsmall removed hremoved i hi q p hpp hshift
  have hhm := hsmall.trans_le (min_le_left dm ds)
  have hhs := hsmall.trans_le (min_le_right dm ds)
  have him := hi.trans_le (min_le_left dm ds)
  apply (hmoment grid w hw n r hn removed hremoved i q h p hh hhm him hshift).trans
  exact mul_le_mul_of_nonneg_left
    (hsurvival grid w hw n h hn hhH hh hhs removed hremoved i q p hpp hshift) (by positivity)

end Luce.Section6
