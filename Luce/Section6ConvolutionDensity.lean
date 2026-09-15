import Luce.Section6IncrementDensity

noncomputable section
open MeasureTheory Set
open scoped Convolution
namespace Luce.Section6

theorem convolutionDensity_nonneg {gamma q : ℝ} (hg : 0 < gamma) (hq : 0 < q)
    (k : ℕ) (x : ℝ) : 0 ≤ convolutionDensity gamma q k x := by
  induction k generalizing x with
  | zero => exact (incrementDensity_pos hg hq x).le
  | succ k ih =>
    change 0 ≤ ∫ t : ℝ, incrementDensity gamma q t*convolutionDensity gamma q k (x-t)
    exact integral_nonneg (fun t => mul_nonneg (incrementDensity_pos hg hq t).le (ih _))

theorem convolutionDensity_integrable {gamma q : ℝ} (hg : 0 < gamma) (hq : 0 < q)
    (k : ℕ) : Integrable (convolutionDensity gamma q k) := by
  induction k with
  | zero => exact incrementDensity_integrable hg hq
  | succ k ih =>
    exact (incrementDensity_integrable hg hq).integrable_convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) ih

theorem convolutionDensity_integral {gamma q : ℝ} (hg : 0 < gamma) (hq : 0 < q)
    (k : ℕ) : (∫ x : ℝ, convolutionDensity gamma q k x) = 1 := by
  induction k with
  | zero => exact incrementDensity_integral hg hq
  | succ k ih =>
    rw [convolutionDensity, integral_convolution _ (incrementDensity_integrable hg hq)
      (convolutionDensity_integrable hg hq k), incrementDensity_integral hg hq, ih]
    simp

theorem convolutionDensity_bound {gamma q : ℝ} (hg : 0 < gamma) (hq : 0 < q)
    (k : ℕ) (x : ℝ) : convolutionDensity gamma q k x ≤ gamma*Real.exp (-1) := by
  induction k generalizing x with
  | zero => exact incrementDensity_bound hg hq x
  | succ k ih =>
    change (∫ t : ℝ, incrementDensity gamma q t*convolutionDensity gamma q k (x-t)) ≤ _
    have hb := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => mul_nonneg (incrementDensity_pos hg hq t).le
        (convolutionDensity_nonneg hg hq k (x-t))))
      ((incrementDensity_integrable hg hq).mul_const (gamma*Real.exp (-1)))
      (Filter.Eventually.of_forall (fun t =>
        mul_le_mul_of_nonneg_left (ih (x-t)) (incrementDensity_pos hg hq t).le))
    apply hb.trans_eq
    rw [integral_mul_const, incrementDensity_integral hg hq, one_mul]

end Luce.Section6
