import Luce.Section6IncrementEnvelope
import Luce.Section6ConvolutionDensity
import Luce.Section6FiniteProductIntegral

noncomputable section
open MeasureTheory Set
open scoped Convolution
namespace Luce.Section6

/-- Analytic hypotheses for a generic logarithmic increment density. -/
structure TraceDensity68 (p : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  continuous : Continuous p
  integrable : Integrable p
  integral_one : (∫ x, p x) = 1
  bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, p x ≤ M

theorem incrementDensity_traceDensity68 {gamma q : ℝ} (hg : 0 < gamma) (hq : 0 < q) :
    TraceDensity68 (incrementDensity gamma q) where
  nonneg x := (incrementDensity_pos hg hq x).le
  continuous := incrementDensity_continuous gamma q
  integrable := incrementDensity_integrable hg hq
  integral_one := incrementDensity_integral hg hq
  bounded := ⟨gamma*Real.exp (-1), by positivity, incrementDensity_bound hg hq⟩

def traceConvolution68 (p : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => p
  | k+1 => p ⋆ traceConvolution68 p k

theorem traceConvolution68_incrementDensity (gamma q : ℝ) (k : ℕ) :
    traceConvolution68 (incrementDensity gamma q) k = convolutionDensity gamma q k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [traceConvolution68, convolutionDensity, ih]

namespace TraceDensity68
variable {p : ℝ → ℝ} (hp : TraceDensity68 p)
include hp

theorem convolution_nonneg (k : ℕ) (x : ℝ) : 0 ≤ traceConvolution68 p k x := by
  induction k generalizing x with
  | zero => exact hp.nonneg x
  | succ k ih =>
    change 0 ≤ ∫ t : ℝ, p t*traceConvolution68 p k (x-t)
    exact integral_nonneg (fun t => mul_nonneg (hp.nonneg t) (ih _))

theorem convolution_integrable (k : ℕ) : Integrable (traceConvolution68 p k) := by
  induction k with
  | zero => exact hp.integrable
  | succ k ih =>
    exact hp.integrable.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) ih

theorem convolution_bound {M : ℝ} (hM : ∀ x, p x ≤ M) (k : ℕ) (x : ℝ) :
    traceConvolution68 p k x ≤ M := by
  induction k generalizing x with
  | zero => exact hM x
  | succ k ih =>
    change (∫ t : ℝ, p t*traceConvolution68 p k (x-t)) ≤ M
    have hb := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => mul_nonneg (hp.nonneg t)
        (hp.convolution_nonneg k (x-t)))) (hp.integrable.mul_const M)
      (Filter.Eventually.of_forall (fun t => mul_le_mul_of_nonneg_left (ih _) (hp.nonneg t)))
    simpa only [integral_mul_const, hp.integral_one, one_mul] using hb

theorem convolution_continuous (k : ℕ) : Continuous (traceConvolution68 p k) := by
  obtain ⟨M, _, hM⟩ := hp.bounded
  induction k with
  | zero => exact hp.continuous
  | succ k ih =>
    apply BddAbove.continuous_convolution_right_of_integrable
      (L := ContinuousLinearMap.lsmul ℝ ℝ) _ hp.integrable ih
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    change ‖traceConvolution68 p k x‖ ≤ M
    rw [Real.norm_eq_abs, abs_of_nonneg (hp.convolution_nonneg k x)]
    exact hp.convolution_bound hM k x

theorem reflect : TraceDensity68 (fun x => p (-x)) where
  nonneg x := hp.nonneg (-x)
  continuous := hp.continuous.comp continuous_neg
  integrable := hp.integrable.comp_neg
  integral_one := (integral_neg_eq_self p volume).trans hp.integral_one
  bounded := by obtain ⟨M, hM0, hM⟩ := hp.bounded; exact ⟨M, hM0, fun x => hM (-x)⟩

end TraceDensity68

theorem traceConvolution68_reflect (p : ℝ → ℝ) (k : ℕ) (x : ℝ) :
    traceConvolution68 (fun t => p (-t)) k x = traceConvolution68 p k (-x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change (∫ t : ℝ, p (-t)*traceConvolution68 (fun t => p (-t)) k (x-t)) =
      ∫ t : ℝ, p t*traceConvolution68 p k (-x-t)
    simp_rw [ih]
    rw [← integral_neg_eq_self (fun t : ℝ => p t*traceConvolution68 p k (-x-t)) volume]
    apply integral_congr_ae
    filter_upwards [] with t
    congr 2
    ring
end Luce.Section6
