import Luce.Section6InteriorShiftedMoment
import Luce.Section6TwoExponentialBounds

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Uniform Lp bound for every source and interior demanded rank. The
remaining rate-dependent exponential remainder will be absorbed using the
profile's global polynomial rate bounds in the global domination argument. -/
theorem PowerProfile.interior_insertion_Lp {f : ℝ → ℝ}
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
      ENNReal.ofReal (C*((w n).rate i/(n : ℝ))*
        (Real.exp (-d*(w n).rate i)+Real.exp (-d*(n : ℝ)))) := by
  obtain ⟨B, d, N, hB, hd, hN, hmoment⟩ := hp.interior_shifted_insertion_moment heps r
  have hp0R : (0 : ℝ) < p0 := Nat.cast_pos.mpr hp0
  have hf : (0 : ℝ) < p0.factorial := Nat.cast_pos.mpr (Nat.factorial_pos p0)
  refine ⟨2*(p0.factorial : ℝ)*B, d/(p0 : ℝ), N, by positivity, div_pos hd hp0R, hN, ?_⟩
  intro grid w hw n h hn hlarge hl hu removed hremoved i q p hshift hpp hpp0
  have hi := (w n).positive i
  have hm := hmoment grid w hw n h hn hlarge hl hu removed hremoved i q p hshift hpp
  have hex := sum_exp_neg_le_twice_min (x := (w n).rate i) (y := (n : ℝ)) hd.le
  have hm2 : (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      2*(p.factorial : ℝ)*(B*((w n).rate i/(n : ℝ)))^p*
        Real.exp (-d*min ((w n).rate i) (n : ℝ)) := by
    have hh := hm.trans (mul_le_mul_of_nonneg_left hex (by positivity))
    nlinarith only [hh]
  have hpower := hm2.trans (uniform_moment_decay hpp hpp0 hB.le
    (by positivity) hd.le (le_min hi.le (Nat.cast_nonneg n)))
  have hnorm := deleted_kernel_eLpNorm_le_of_moment (w n) removed i q.val p (by omega)
    (by positivity) hpower
  apply hnorm.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (exp_neg_min_le_sum (d/(p0 : ℝ)) ((w n).rate i) (n : ℝ))
    (by positivity)

end Luce.Section6
