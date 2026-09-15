import Luce.Section6RightOutsideLp
import Luce.Section6RightRemainder

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

theorem PowerProfile.right_outside_insertion_envelope {f : ℝ → ℝ}
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
      ENNReal.ofReal (C*(((w n).rate i*((n : ℝ)/(h : ℝ))^beta/(h : ℝ))*
        Real.exp (-d*((w n).rate i*((n : ℝ)/(h : ℝ))^beta))+
          Real.exp (-d*(n : ℝ)^(beta/(beta+1))))) := by
  obtain ⟨B, d, H, delta, N, hB, hd, hH, hdelta, hdelta1, hN, hb⟩ :=
    hp.right_outside_insertion_Lp hsigma hsigma1 r p0 hp0
  have hz := (right_extreme_exponent_bounds hp.2.2.2.1.2.1).1
  obtain ⟨A, hA, ha⟩ := hp.right_rate_remainder hd hz
  refine ⟨B*(1+A), d/2, H, delta, N, by positivity, half_pos hd,
    hH, hdelta, hdelta1, hN, ?_⟩
  intro grid w hw n h hn hnN hhH hh hsmall removed hremoved i hi q p hpp hpp0 hshift
  apply (hb grid w hw n h hn hnN hhH hh hsmall removed hremoved i hi q p hpp hpp0 hshift).trans
  apply ENNReal.ofReal_le_ofReal
  let x := (w n).rate i*((n : ℝ)/(h : ℝ))^beta
  let y := (n : ℝ)^(beta/(beta+1))
  let z := x/(h : ℝ)
  have hir := (w n).positive i
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hz0 : 0 ≤ z := div_nonneg hx hhR.le
  have he : Real.exp (-d*x) ≤ Real.exp (-(d/2)*x) := Real.exp_le_exp.mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_left he hz0
  have hr := ha grid w hw n h i (by omega)
  change z*Real.exp (-d*y) ≤ A*Real.exp (-(d/2)*y) at hr
  change B*z*(Real.exp (-d*x)+Real.exp (-d*y)) ≤
    (B*(1+A))*(z*Real.exp (-(d/2)*x)+Real.exp (-(d/2)*y))
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hm hr) hB.le
  have hextra := mul_nonneg (mul_nonneg hB.le hA.le)
    (mul_nonneg hz0 (Real.exp_pos (-(d/2)*x)).le)
  have hbase : 0 ≤ B*Real.exp (-(d/2)*y) := by positivity
  nlinarith

end Luce.Section6
