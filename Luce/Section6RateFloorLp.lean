import Luce.Section6LeftUnrestrictedLp

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Generic rate-floor norm conversion. Concrete endpoint results must
derive the floor; it is not an allowed additional model assumption. -/
theorem deleted_kernel_Lp_of_rate_floor {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n)
    (q : Fin (Finset.univ \ removed).card) (p p0 : ℕ)
    (hpp : 1 ≤ p) (hpp0 : p ≤ p0) {W : ℝ} (hW : 0 < W)
    (hfloor : ∀ σ, W ≤ orderedRemainingRate (compactDeletedWeights w removed) σ q) :
    eLpNorm (fun old => (deletedGapKernel w removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace w) ≤
      ENNReal.ofReal ((2*(p0.factorial : ℝ))*(w.rate i/W)) := by
  have hi := w.positive i
  have hz : 0 ≤ w.rate i/W := by positivity
  apply deleted_kernel_eLpNorm_le_of_moment w removed i q.val p (by omega) (by positivity)
  have hh := (deleted_kernel_moment_bound_of_rate_floor w removed i q p hW hfloor).trans
    (mul_le_mul_of_nonneg_left (deleted_survival_integral_le_one w removed i q p) (by positivity))
  simp only [mul_one] at hh
  have hd := uniform_moment_decay hpp hpp0 (B := 1) (z := w.rate i/
      W) (d := 0) (x := 0)
      zero_le_one hz (le_refl 0) (le_refl 0)
  simp only [one_mul, neg_zero, zero_mul, Real.exp_zero, mul_one, zero_div] at hd
  apply hh.trans
  apply le_trans ?_ hd
  nlinarith [pow_nonneg hz p, Nat.cast_nonneg (α := ℝ) p.factorial]

end Luce.Section6
