import Luce.Section6RightOutsideEnvelope
import Luce.Section6EndpointEnvelopeTarget

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Outside sources obey the inverse target-depth estimate, with all
constants obtained from the original sampled profile. -/
theorem PowerProfile.right_outside_insertion_target_bound {f : ℝ → ℝ}
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
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (C/(h : ℝ)) := by
  obtain ⟨B, d, H, delta, N, hB, hd, hH, hdelta, hdelta1, hN, hb⟩ :=
    hp.right_outside_insertion_envelope hsigma hsigma1 r p0 hp0
  have hbeta : 0 < beta := hp.2.2.2.1.2.1
  have hnu : 0 < beta/(beta+1) := div_pos hbeta (by linarith)
  obtain ⟨D, hD, hdecay⟩ := stretched_exp_le_inverse_depth hd hnu
  refine ⟨B*(Real.exp (-1)/d+D), H, delta, N, by positivity,
    hH, hdelta, hdelta1, hN, ?_⟩
  intro grid w hw n h hn hnN hhH hh hsmall removed hremoved i hi q p hpp hpp0 hshift
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hhn : (h : ℝ) ≤ n := by
    have ht := (div_lt_iff₀ hnR).mp (hsmall.trans hdelta1)
    linarith
  let x := (w n).rate i*((n : ℝ)/(h : ℝ))^beta
  have hx : x*Real.exp (-d*x) ≤ Real.exp (-1)/d := by
    simpa [rateKernel, survivalKernel] using rateKernel_le_exp_neg_one_div (a := x) hd
  have ho : (x/(h : ℝ))*Real.exp (-d*x) ≤ (Real.exp (-1)/d)/(h : ℝ) := by
    simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hx hhR.le
  have he : Real.exp (-d*(n : ℝ)^(beta/(beta+1))) ≤ D/(h : ℝ) :=
    (hdecay n hn).trans (div_le_div_of_nonneg_left hD.le hhR hhn)
  apply (hb grid w hw n h hn hnN hhH hh hsmall removed hremoved i hi q p hpp hpp0 hshift).trans
  apply ENNReal.ofReal_le_ofReal
  have ht := mul_le_mul_of_nonneg_left (add_le_add ho he) hB.le
  simpa only [x, ← add_div, mul_div_assoc] using ht

end Luce.Section6
