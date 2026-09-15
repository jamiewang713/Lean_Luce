import Luce.Section6LeftUnrestrictedLp
import Luce.Section6BoundedScaleEnvelope

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

theorem left_rate_floor_ratio {C n h alpha t : ℝ}
    (hC : 0 < C) (hn : 0 < n) (hh : 0 < h) :
    t/(C*n^alpha*h^(1-alpha)) = (1/C)*(t*(h/n)^alpha/h) := by
  rw [Real.div_rpow hh.le hn.le, show (1-alpha : ℝ) = 1+(-alpha) by ring,
    Real.rpow_add hh, Real.rpow_one, Real.rpow_neg hh.le]
  field_simp [hC.ne', hh.ne', (Real.rpow_pos_of_pos hn alpha).ne',
    (Real.rpow_pos_of_pos hh alpha).ne']

/-- Actual left insertion norms for sources outside a fixed left block.
The ordinary exponential kernel is recovered from a bounded scale; no
unjustified assertion that this scale is below one is used. -/
theorem PowerProfile.left_outside_insertion_Lp {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (p0 : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ sigma ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 0 < n → ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    4*r+4 ≤ q.val → (q.val : ℝ)/(n : ℝ) ≤ delta →
    sigma ≤ ((i.val : ℝ)+1)/(n : ℝ) → 1 ≤ p → p ≤ p0 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*((w n).rate i*((q.val : ℝ)/(n : ℝ))^alpha/(q.val : ℝ))*
        Real.exp (-((w n).rate i*((q.val : ℝ)/(n : ℝ))^alpha))) := by
  obtain ⟨A, eps, hA, heps, heps1, hb⟩ := hp.left_unrestricted_insertion_Lp p0
  obtain ⟨B, hB, hscale⟩ := hp.left_outside_scaled_rate_bounded hsigma hsigma1
  refine ⟨(2*(p0.factorial : ℝ))*(1/A)*Real.exp B, min sigma (eps/4),
    by positivity, lt_min hsigma (by positivity), min_le_left _ _, ?_⟩
  intro grid w hw n r hn removed hremoved i q p hq hsmall hi hpp hpp0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hqR : (0 : ℝ) < q.val := Nat.cast_pos.mpr (by omega)
  have hqn : (q.val : ℝ) ≤ eps*(n : ℝ)/4 := by
    have hh := (div_le_iff₀ hnR).mp (hsmall.trans (min_le_right _ _))
    nlinarith
  apply (hb grid w hw n r hn removed hremoved i q p hq hqn hpp hpp0).trans
  apply ENNReal.ofReal_le_ofReal
  rw [left_rate_floor_ratio hA hnR hqR]
  have hir := (w n).positive i
  have hx := hscale grid w hw n q.val i (hsmall.trans (min_le_left _ _)) hi
  have he := restore_bounded_exponential
    (z := (w n).rate i*((q.val : ℝ)/(n : ℝ))^alpha/(q.val : ℝ))
    (by positivity) hx
  have hh := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (2*(p0.factorial : ℝ))*(1/A) by positivity)
  simpa only [mul_assoc] using hh

end Luce.Section6
