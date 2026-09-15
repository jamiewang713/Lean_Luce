import Luce.Section6RightComparisonDepth
import Luce.Section6ExtremeScale

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- The manuscript's right extreme Laplace estimate. In the small-h branch
the comparison depth is a^(beta/(beta+1)), so the proof uses a different
deterministic time. All survivor means and rate bounds are discharged. -/
theorem PowerProfile.right_extreme_survival {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r : ℕ) :
    ∃ d H delta : ℝ, 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ i : Fin n, H ≤ (terminalDepth i : ℝ) → (terminalDepth i : ℝ)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p →
    Nat.dist q.val (n-h) ≤ r+1 →
    (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*raceGapStart (compactDeletedClocks removed old) q))
      ∂exponentialRace (w n)) ≤
      2*(Real.exp (-d*((terminalDepth i : ℝ)/(h : ℝ))^beta)+
        Real.exp (-d*(terminalDepth i : ℝ)^(beta/(beta+1)))) := by
  obtain ⟨d1, H1, delta1, hd1, hH1, hdelta1, hdelta11, hcomp⟩ := hp.right_comparison_depth_survival r
  obtain ⟨d2, H2, delta2, hd2, hH2, hdelta2, hdelta21, htyp⟩ := hp.right_survival_envelope r
  have hb : 0 < beta := hp.2.2.2.1.2.1
  obtain ⟨A, hA, hcut⟩ := right_extreme_depth_cutoff hH1 hb
  refine ⟨min d1 d2, max A H2, min delta1 delta2, lt_min hd1 hd2,
    hA.trans_le (le_max_left _ _), lt_min hdelta1 hdelta2,
    (min_le_left _ _).trans_lt hdelta11, ?_⟩
  intro grid w hw n h hn hhH hh hsmall removed hremoved i hiH hismall q p hpp hshift
  let a : ℝ := terminalDepth i
  let y : ℝ := a^(beta/(beta+1))
  let x : ℝ := (a/(h : ℝ))^beta
  have ha0 : 0 < a := Nat.cast_pos.mpr (terminalDepth_pos i)
  have hcut' := hcut a ((le_max_left _ _).trans hiH)
  have hy : 0 ≤ y := Real.rpow_nonneg ha0.le _
  have hx : 0 ≤ x := Real.rpow_nonneg (by positivity) _
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hysmall : y/(n : ℝ) < delta1 :=
    (div_le_div_of_nonneg_right (right_extreme_depth_le hcut'.1 hb) hnR.le).trans_lt
      (hismall.trans_le (min_le_left _ _))
  have hdy1 : Real.exp (-d1*y) ≤ Real.exp (-(min d1 d2)*y) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right (min_le_left d1 d2) hy])
  have hdx2 : Real.exp (-d2*x) ≤ Real.exp (-(min d1 d2)*x) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right (min_le_right d1 d2) hx])
  change _ ≤ 2*(Real.exp (-(min d1 d2)*x)+Real.exp (-(min d1 d2)*y))
  by_cases hhy : (h : ℝ) ≤ y
  · have he := hcomp grid w hw n h y hn hcut'.2 hh hhy hysmall removed hremoved i q p hpp hshift
    have hscale : ((terminalDepth i : ℝ)/y)^beta = y := right_extreme_scale_identity ha0 hb
    rw [hscale] at he
    nlinarith [Real.exp_pos (-(min d1 d2)*x)]
  · have he := htyp grid w hw n h hn ((le_max_right _ _).trans hhH) hh
      (hsmall.trans_le (min_le_right _ _)) removed hremoved i q p hpp hshift
    have hdy2 : Real.exp (-d2*(h : ℝ)) ≤ Real.exp (-(min d1 d2)*y) := by
      apply Real.exp_le_exp.mpr
      have hless : y ≤ (h : ℝ) := (lt_of_not_ge hhy).le
      nlinarith [mul_le_mul_of_nonneg_left hless hd2.le,
        mul_le_mul_of_nonneg_right (min_le_right d1 d2) hy]
    change _ ≤ Real.exp (-d2*x)+Real.exp (-d2*(h : ℝ)) at he
    nlinarith [Real.exp_pos (-(min d1 d2)*x), Real.exp_pos (-(min d1 d2)*y)]

end Luce.Section6
