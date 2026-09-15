import Luce.Section6InteriorInsertionLp
import Luce.Section6InteriorRemainder

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The manuscript's ordinary middle kernel plus a source-uniform
exponential remainder, for the actual deleted insertion factor. -/
theorem PowerProfile.interior_insertion_envelope {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d N : ℝ, 0 < C ∧ 0 < d ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → N ≤ (n : ℝ) →
    eps*(n : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ (1-eps)*(n : ℝ) →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    Nat.dist q.val (h-1) ≤ r+1 → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*(((w n).rate i/(n : ℝ))*Real.exp (-d*(w n).rate i)+
        Real.exp (-d*(n : ℝ)))) := by
  obtain ⟨B, d, N, hB, hd, hN, hb⟩ := hp.interior_insertion_Lp heps r p0 hp0
  obtain ⟨A, hA, ha⟩ := hp.interior_rate_remainder hd
  refine ⟨B*(1+A), d/2, N, by positivity, half_pos hd, hN, ?_⟩
  intro grid w hw n h hn hlarge hl hu removed hremoved i q p hshift hpp hpp0
  apply (hb grid w hw n h hn hlarge hl hu removed hremoved i q p hshift hpp hpp0).trans
  apply ENNReal.ofReal_le_ofReal
  have hi := (w n).positive i
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hx : 0 ≤ (w n).rate i/(n : ℝ) := div_nonneg hi.le hnR.le
  have hdec : Real.exp (-d*(w n).rate i) ≤ Real.exp (-(d/2)*(w n).rate i) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hmain := mul_le_mul_of_nonneg_left hdec hx
  have hrem := ha grid w hw n i
  have he1 := Real.exp_pos (-(d/2)*(w n).rate i)
  have he2 := Real.exp_pos (-(d/2)*(n : ℝ))
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hmain hrem) hB.le
  have hextra := mul_nonneg (mul_nonneg hB.le hA.le) (mul_nonneg hx he1.le)
  nlinarith

end Luce.Section6
