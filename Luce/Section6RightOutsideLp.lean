import Luce.Section6RightOutsideSurvival
import Luce.Section6RightUnrestrictedMoment
import Luce.Section6UniformMomentDecay
import Luce.Section6TwoExponentialBounds

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

theorem PowerProfile.right_outside_insertion_Lp {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d H delta N : ℝ, 0 < C ∧ 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → N ≤ (n : ℝ) → H ≤ (h : ℝ) →
    8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n), sigma ≤ (terminalDepth i : ℝ)/(n : ℝ) →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
    Nat.dist q.val (n-h) ≤ r+1 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*((w n).rate i*((n : ℝ)/(h : ℝ))^beta/(h : ℝ))*
        (Real.exp (-d*((w n).rate i*((n : ℝ)/(h : ℝ))^beta))+
          Real.exp (-d*(n : ℝ)^(beta/(beta+1))))) := by
  obtain ⟨B, hB, hm⟩ := hp.right_unrestricted_shifted_moment
  obtain ⟨d, H, delta, N, hd, hH, hdelta, hdelta1, hN, hs⟩ := hp.right_outside_survival hsigma hsigma1 r
  have hp0R : (0 : ℝ) < p0 := Nat.cast_pos.mpr hp0
  refine ⟨4*(p0.factorial : ℝ)*B, d/(p0 : ℝ), H, delta, N,
    by positivity, div_pos hd hp0R, hH, hdelta, hdelta1, hN, ?_⟩
  intro grid w hw n h hn hnN hhH hh hsmall removed hremoved i hi q p hpp hpp0 hshift
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hhn : h ≤ n := Nat.le_of_lt (Nat.cast_lt.mp ((div_lt_one hnR).mp (hsmall.trans hdelta1)))
  have hir := (w n).positive i
  let x := (w n).rate i*((n : ℝ)/(h : ℝ))^beta
  let y := (n : ℝ)^(beta/(beta+1))
  let z := x/(h : ℝ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := Real.rpow_nonneg hnR.le _
  have hz : 0 ≤ z := div_nonneg hx hhR.le
  have hm0 := hm grid w hw n r h hn hhn hh removed hremoved i q p hshift
  have hs0 := hs grid w hw n h hn hnN hhH hh hsmall removed hremoved i hi q p hpp hshift
  have he := sum_exp_neg_le_twice_min (x := x) (y := y) hd.le
  have hm1 : (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      4*(p.factorial : ℝ)*(B*z)^p*Real.exp (-d*min x y) := by
    have hh1 := hm0.trans (mul_le_mul_of_nonneg_left hs0 (by positivity))
    have hh2 := mul_le_mul_of_nonneg_left he (show 0 ≤ 2*(p.factorial : ℝ)*(B*z)^p by positivity)
    change _ ≤ (p.factorial : ℝ)*(B*z)^p*(2*(Real.exp (-d*x)+Real.exp (-d*y))) at hh1
    nlinarith only [hh1, hh2]
  have hpow : 2*(B*z)^p ≤ (2*B*z)^p := by
    have hp2 : (2 : ℝ) ≤ 2^p := le_self_pow₀ (by norm_num) (by omega)
    have hh2 := mul_le_mul_of_nonneg_right hp2 (show 0 ≤ B^p*z^p by positivity)
    simpa only [mul_pow, mul_assoc] using hh2
  have hm2 : (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      2*(p.factorial : ℝ)*(2*B*z)^p*Real.exp (-d*min x y) := by
    have hh2 := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ 2*(p.factorial : ℝ)*Real.exp (-d*min x y) by positivity)
    nlinarith only [hm1, hh2]
  have hd0 := uniform_moment_decay hpp hpp0 (B := 2*B) (by positivity) hz hd.le (le_min hx hy)
  have hnorm := deleted_kernel_eLpNorm_le_of_moment (w n) removed i q.val p (by omega)
    (by positivity) (hm2.trans hd0)
  apply hnorm.trans
  apply ENNReal.ofReal_le_ofReal
  have he0 := mul_le_mul_of_nonneg_left (exp_neg_min_le_sum (d/(p0 : ℝ)) x y)
    (show 0 ≤ 4*(p0.factorial : ℝ)*B*z by positivity)
  change _ ≤ (4*(p0.factorial : ℝ)*B)*z*(Real.exp (-(d/(p0 : ℝ))*x)+Real.exp (-(d/(p0 : ℝ))*y))
  nlinarith only [he0]

end Luce.Section6

