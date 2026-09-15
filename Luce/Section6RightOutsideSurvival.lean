import Luce.Section6RightComparisonRate
import Luce.Section6SublinearCutoff
import Luce.Section6OutsideSourceRates
import Luce.Section6ExtremeScale

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Outside-right survival with the actual ordinary rate-time exponent and
a stretched-exponential remainder in the row size. The different comparison
time in the small-depth branch and all rate/mean bounds are proved. -/
theorem PowerProfile.right_outside_survival {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (r : ℕ) :
    ∃ d H delta N : ℝ, 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → N ≤ (n : ℝ) → H ≤ (h : ℝ) →
    8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n), sigma ≤ (terminalDepth i : ℝ)/(n : ℝ) →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p →
    Nat.dist q.val (n-h) ≤ r+1 →
    (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*raceGapStart (compactDeletedClocks removed old) q))
      ∂exponentialRace (w n)) ≤
      2*(Real.exp (-d*((w n).rate i*((n : ℝ)/(h : ℝ))^beta))+
        Real.exp (-d*(n : ℝ)^(beta/(beta+1)))) := by
  obtain ⟨d0, H, delta, hd0, hH, hdelta, hdelta1, hb⟩ := hp.right_comparison_depth_survival_rate r
  obtain ⟨b, hb0, hrate⟩ := hp.sampled_lower_outside_right hsigma hsigma1
  have hbeta : 0 < beta := hp.2.2.2.1.2.1
  have hz := right_extreme_exponent_bounds hbeta
  obtain ⟨N, hN, hcut⟩ := sublinear_power_cutoff (H := H) hz.1 hz.2 hdelta
  let d := min (d0*b) d0
  have hd : 0 < d := lt_min (mul_pos hd0 hb0) hd0
  have hdd : d ≤ d0 := min_le_right _ _
  refine ⟨d, H, delta, N, hd, hH, hdelta, hdelta1, hN, ?_⟩
  intro grid w hw n h hn hnN hhH hh hsmall removed hremoved i hi q p hpp hshift
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  obtain ⟨hn1, hyH, hysmall⟩ := hcut (n : ℝ) hnN
  let y := (n : ℝ)^(beta/(beta+1))
  let x := (w n).rate i*((n : ℝ)/(h : ℝ))^beta
  have hy : 0 < y := Real.rpow_pos_of_pos hnR _
  have hir := (w n).positive i
  have hx : 0 ≤ x := by dsimp [x]; positivity
  change _ ≤ 2*(Real.exp (-d*x)+Real.exp (-d*y))
  by_cases hhy : (h : ℝ) ≤ y
  · have he := hb grid w hw n h y hn hyH hh hhy hysmall removed hremoved i q p hpp hshift
    have hscale : ((n : ℝ)/y)^beta = y := right_extreme_scale_identity hnR hbeta
    rw [hscale] at he
    have hcoef : d ≤ d0*(w n).rate i := (min_le_left _ _).trans
      (mul_le_mul_of_nonneg_left (hrate grid w hw n i hi) hd0.le)
    have he1 : Real.exp (-d0*((w n).rate i*y)) ≤ Real.exp (-d*y) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hcoef hy.le]
    have he2 : Real.exp (-d0*y) ≤ Real.exp (-d*y) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hdd hy.le]
    nlinarith [Real.exp_pos (-d*x)]
  · have he := hb grid w hw n h (h : ℝ) hn hhH hh (le_refl _) hsmall removed hremoved i q p hpp hshift
    change _ ≤ Real.exp (-d0*x)+Real.exp (-d0*(h : ℝ)) at he
    have he1 : Real.exp (-d0*x) ≤ Real.exp (-d*x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hdd hx]
    have he2 : Real.exp (-d0*(h : ℝ)) ≤ Real.exp (-d*y) := by
      apply Real.exp_le_exp.mpr
      have hless : y ≤ (h : ℝ) := (lt_of_not_ge hhy).le
      nlinarith [mul_le_mul_of_nonneg_left hless hd0.le,
        mul_le_mul_of_nonneg_right hdd hy.le]
    nlinarith [Real.exp_pos (-d*x), Real.exp_pos (-d*y)]

end Luce.Section6
