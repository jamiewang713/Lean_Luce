import Luce.Section6TerminalReference
import Luce.Section6RightOutsideSurvival
import Luce.Section6UniformMomentDecay

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Terminal-window insertion norms, including the infinite final gap,
for sources outside a fixed active-right block. -/
theorem PowerProfile.terminal_outside_right_Lp {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (r Q p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d N : ℝ, 0 < C ∧ 0 < d ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (k p : ℕ), sigma ≤ (terminalDepth i : ℝ)/(n : ℝ) →
    (Finset.univ \ removed).card ≤ k+Q → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i k).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*Real.exp (-d*(n : ℝ)^(beta/(beta+1)))) := by
  obtain ⟨d0, H, delta, hd0, hH, hdelta, hdelta1, hs⟩ := hp.right_comparison_depth_survival_rate r
  obtain ⟨b, hb, hrate⟩ := hp.sampled_lower_outside_right hsigma hsigma1
  have hbeta : 0 < beta := hp.2.2.2.1.2.1
  have hzz := right_extreme_exponent_bounds hbeta
  let h : ℕ := 8*r+Q+8
  obtain ⟨N, hN, hcut⟩ := sublinear_power_cutoff (H := max H ((h : ℝ)+1)) hzz.1 hzz.2 hdelta
  let d := min (d0*b) d0
  have hd : 0 < d := lt_min (mul_pos hd0 hb) hd0
  have hp0R : (0 : ℝ) < p0 := Nat.cast_pos.mpr hp0
  refine ⟨2*(p0.factorial : ℝ), d/(p0 : ℝ), N, by positivity, div_pos hd hp0R, hN, ?_⟩
  intro grid w hw n hn hlarge removed hremoved i k p hi hk hpp hpp0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨hn1, hyH, hysmall⟩ := hcut (n : ℝ) hlarge
  let y := (n : ℝ)^(beta/(beta+1))
  have hy : 0 < y := Real.rpow_pos_of_pos hnR _
  have hhy : (h : ℝ)+1 ≤ y := (le_max_right _ _).trans hyH
  have hyn : y ≤ (n : ℝ) := right_extreme_depth_le hn1 hbeta
  have hhn : h < n := by exact_mod_cast (show (h : ℝ) < n by linarith)
  obtain ⟨q, hq, hqk⟩ := terminal_window_reference_gap removed (by dsimp [h]; omega) hhn hk
  have hshift : Nat.dist q.val (n-h) ≤ r+1 := by rw [hq]; simp
  have hs0 := hs grid w hw n h y hn ((le_max_left _ _).trans hyH)
    (by dsimp [h]; omega) (by linarith) hysmall removed hremoved i q p hpp hshift
  have hscale : ((n : ℝ)/y)^beta = y := right_extreme_scale_identity hnR hbeta
  rw [hscale] at hs0
  have hcoef : d ≤ d0*(w n).rate i := (min_le_left _ _).trans
    (mul_le_mul_of_nonneg_left (hrate grid w hw n i hi) hd0.le)
  have he1 : Real.exp (-d0*((w n).rate i*y)) ≤ Real.exp (-d*y) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hcoef hy.le]
  have he2 : Real.exp (-d0*y) ≤ Real.exp (-d*y) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (show d ≤ d0 from min_le_right _ _) hy.le]
  have hm : (∫ old, (deletedGapKernel (w n) removed old i k).toReal^p ∂exponentialRace (w n)) ≤
      2*Real.exp (-d*y) := by
    have hh0 := (deleted_gap_moment_le_earlier_survival (w n) removed i q k p hqk).trans hs0
    nlinarith only [hh0, he1, he2]
  have hfact : (1 : ℝ) ≤ p.factorial := by exact_mod_cast Nat.factorial_pos p
  have hm' : (∫ old, (deletedGapKernel (w n) removed old i k).toReal^p ∂exponentialRace (w n)) ≤
      2*(p.factorial : ℝ)*(1*1)^p*Real.exp (-d*y) := by
    simp only [mul_one, one_pow]
    nlinarith [Real.exp_pos (-d*y)]
  have hpw := hm'.trans (uniform_moment_decay hpp hpp0 (B := 1) (z := 1)
    zero_le_one zero_le_one hd.le hy.le)
  have he := deleted_kernel_eLpNorm_le_of_moment (w n) removed i k p (by omega) (by positivity) hpw
  simpa only [mul_one] using he

end Luce.Section6
