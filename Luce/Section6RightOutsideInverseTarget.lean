import Luce.Section6OutsideRightInverseRow
import Luce.Section6RightOutsideEnvelope
import Luce.Section6EndpointEnvelopeTarget
import Luce.Section6OutsideSourceRates

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The actual outside-right insertion estimate is inverse row size.
Its local rate floor and all decay constants follow from the profile. -/
theorem PowerProfile.right_outside_insertion_inverse_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C H delta N : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → N ≤ (n : ℝ) → H ≤ (h : ℝ) →
    8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n), sigma ≤ (terminalDepth i : ℝ)/(n : ℝ) →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
    Nat.dist q.val (n-h) ≤ r+1 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (C/(n : ℝ)) := by
  obtain ⟨B, d, H, delta, N, hB, hd, hH, hdelta, hdelta1, hN, hb⟩ :=
    hp.right_outside_insertion_envelope hsigma hsigma1 r p0 hp0
  obtain ⟨b, hbpos, hrate⟩ := hp.sampled_lower_outside_right hsigma hsigma1
  have hbeta : 0 < beta := hp.2.2.2.1.2.1
  obtain ⟨A, hA, ha⟩ := outside_right_kernel_inverse_row hbeta hbpos hd
  obtain ⟨D, hD, hdecay⟩ := stretched_exp_le_inverse_depth hd
    (show 0 < beta/(beta+1) from div_pos hbeta (by linarith))
  refine ⟨B*(A+D), H, delta, N, mul_pos hB (add_pos hA hD), hH, hdelta, hdelta1, hN, ?_⟩
  intro grid w hw n h hn hnN hhH hh hsmall removed hremoved i hi q p hpp hpp0 hshift
  have ho := ha (n : ℝ) (h : ℝ) ((w n).rate i) (Nat.cast_pos.mpr hn)
    (Nat.cast_pos.mpr (by omega)) (hrate grid w hw n i hi)
  have he := hdecay n hn
  apply (hb grid w hw n h hn hnN hhH hh hsmall removed hremoved i hi q p hpp hpp0 hshift).trans
  apply ENNReal.ofReal_le_ofReal
  have ht := mul_le_mul_of_nonneg_left (add_le_add ho he) hB.le
  simpa only [← add_div, mul_div_assoc] using ht

end Luce.Section6
