import Luce.Section65MomentRemainder
import Mathlib.MeasureTheory.Measure.LevyConvergence

noncomputable section
open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology BigOperators NNReal
namespace Luce.Section6

theorem momentTaylor_tendsto (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    (h : ∀ k : ℕ, Tendsto (fun n => ∫ x, x^k ∂μ n) atTop (𝓝 (∫ x, x^k ∂ν)))
    (m : ℕ) : Tendsto (fun n => momentTaylor (μ n) m) atTop (𝓝 (momentTaylor ν m)) := by
  unfold momentTaylor
  apply tendsto_finsetSum
  intro j hj
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp (h j)).const_mul _

/-- Moment convergence to a law with an integrable exponential envelope
implies characteristic convergence, using finite Taylor polynomials only.
No exponential moment of the approximating laws is required. -/
theorem charFun_one_tendsto_of_moments (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    (hμ : ∀ n k : ℕ, MemLp id k (μ n)) (hν : ∀ k : ℕ, MemLp id k ν)
    (he : Integrable (fun x : ℝ => Real.exp (2*|x|)) ν)
    (h : ∀ k : ℕ, Tendsto (fun n => ∫ x, x^k ∂μ n) atTop (𝓝 (∫ x, x^k ∂ν))) :
    Tendsto (fun n => charFun (μ n) 1) atTop (𝓝 (charFun ν 1)) := by
  apply complex_tendsto_of_finite_approximations
    (fun n => charFun (μ n) 1) (charFun ν 1)
    (fun m n => momentTaylor (μ n) (2*m+1)) (fun m => momentTaylor ν (2*m+1))
    (fun m n => (∫ x, |x|^(2*m+1+1) ∂μ n)/((2*m+1).factorial : ℝ))
    (fun m => (∫ x, |x|^(2*m+1+1) ∂ν)/((2*m+1).factorial : ℝ))
  · intro m n
    exact charFun_momentTaylor_bound (μ n) (hμ n) (2*m+1)
  · intro m
    exact charFun_momentTaylor_bound ν hν (2*m+1)
  · intro m
    exact momentTaylor_tendsto μ ν h (2*m+1)
  · intro m
    have heven : Even (2*m+1+1) := ⟨m+1, by omega⟩
    simp_rw [heven.pow_abs]
    exact (h (2*m+1+1)).div_const _
  · exact (moment_remainder_tendsto ν he).comp
      (tendsto_atTop.mpr (fun b => eventually_atTop.mpr ⟨b, fun n hn => by omega⟩))

theorem gaussian_charFun_one_tendsto_of_moments (μ : ℕ → Measure ℝ)
    [∀ n, IsFiniteMeasure (μ n)] (v : ℝ≥0)
    (hμ : ∀ n k : ℕ, MemLp id k (μ n))
    (h : ∀ k : ℕ, Tendsto (fun n => ∫ x, x^k ∂μ n) atTop (𝓝 (∫ x, x^k ∂gaussianReal 0 v))) :
    Tendsto (fun n => charFun (μ n) 1) atTop (𝓝 (Complex.exp (-(v : ℂ)/2))) := by
  have hh := charFun_one_tendsto_of_moments μ (gaussianReal 0 v) hμ
    (fun k => memLp_id_gaussianReal (k : ℝ≥0))
    (integrable_exp_mul_abs (integrable_exp_mul_gaussianReal 2) (integrable_exp_mul_gaussianReal (-2))) h
  simpa [charFun_gaussianReal, neg_div] using hh

end Luce.Section6
