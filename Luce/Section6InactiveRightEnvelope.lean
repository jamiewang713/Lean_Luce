import Luce.Section6InactiveRightLp
import Luce.Section6LogarithmicRemainder

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The inactive terminal kernel with its rate prefactor absorbed in the
exceptional term, preserving sqrt(n*h). Fixed final gaps are separate. -/
theorem PowerProfile.inactive_right_insertion_envelope {f : ℝ → ℝ}
    {left : EndpointBehavior} {c : ℝ} (hp : PowerProfile f left (.finite c))
    (p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r h : ℕ, 8 ≤ n → 16*r ≤ n → 8*r+8 ≤ h → 16384*h ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    Nat.dist q.val (n-h) ≤ r+1 → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*(((w n).rate i/(h : ℝ))*
        Real.exp (-d*((w n).rate i*Real.log ((n : ℝ)/(h : ℝ))))+
          Real.exp (-d*Real.sqrt ((n : ℝ)*(h : ℝ))))) := by
  obtain ⟨B, d, hB, hd, hb⟩ := hp.inactive_right_insertion_Lp p0 hp0
  obtain ⟨A, hA, ha⟩ := hp.logarithmic_rate_remainder hd
  refine ⟨B*(1+A), d/2, by positivity, half_pos hd, ?_⟩
  intro grid w hw n r h hn hr hh hsmall removed hremoved i q p hshift hpp hpp0
  apply (hb grid w hw n r h hn hr hh hsmall removed hremoved i q p hshift hpp hpp0).trans
  apply ENNReal.ofReal_le_ofReal
  let x := (w n).rate i*Real.log ((n : ℝ)/(h : ℝ))
  let y := Real.sqrt ((n : ℝ)*(h : ℝ))
  let z := (w n).rate i/(h : ℝ)
  have hir := (w n).positive i
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hhnR : (h : ℝ) ≤ n := by exact_mod_cast (show h ≤ n by omega)
  have hl := Real.log_nonneg ((one_le_div hhR).mpr hhnR)
  have hx : 0 ≤ x := mul_nonneg hir.le hl
  have hz0 : 0 ≤ z := div_nonneg hir.le hhR.le
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
