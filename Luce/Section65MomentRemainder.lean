import Luce.Section65TaylorBound
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Distributions.Gaussian.Real

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal
namespace Luce.Section6

theorem moment_remainder_tendsto (μ : Measure ℝ)
    (he : Integrable (fun x : ℝ => Real.exp (2*|x|)) μ) :
    Tendsto (fun n : ℕ => (∫ x, |x|^(n+1) ∂μ)/(n.factorial : ℝ)) atTop (𝓝 0) := by
  have hp (n : ℕ) (x : ℝ) : |x|^(n+1)/(n.factorial : ℝ) ≤ Real.exp (2*|x|) := by
    have hpow := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n
    have hx : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
    calc
      _ = |x| * (|x|^n/(n.factorial : ℝ)) := by rw [pow_succ']; ring
      _ ≤ Real.exp |x| * Real.exp |x| := mul_le_mul hx hpow (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hh := tendsto_integral_of_dominated_convergence (f := fun _ : ℝ => (0 : ℝ))
    (fun x : ℝ => Real.exp (2*|x|))
    (fun n : ℕ => (show AEStronglyMeasurable (fun x : ℝ => |x|^(n+1)/(n.factorial : ℝ)) μ by fun_prop))
    he (fun n => ae_of_all μ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |x|^(n+1)/(n.factorial : ℝ))]
      exact hp n x))
    (ae_of_all μ (fun x => ?_))
  · simpa only [integral_div, integral_zero] using hh
  have ht := (Real.summable_pow_div_factorial |x|).tendsto_atTop_zero.const_mul |x|
  simpa only [pow_succ', mul_div_assoc, mul_zero] using ht

theorem gaussian_moment_remainder_tendsto (v : ℝ≥0) :
    Tendsto (fun n : ℕ => (∫ x, |x|^(n+1) ∂gaussianReal 0 v)/(n.factorial : ℝ))
      atTop (𝓝 0) := by
  apply moment_remainder_tendsto
  exact integrable_exp_mul_abs (integrable_exp_mul_gaussianReal 2)
    (integrable_exp_mul_gaussianReal (-2))

theorem complex_tendsto_of_finite_approximations
    (u : ℕ → ℂ) (v : ℂ) (p : ℕ → ℕ → ℂ) (q : ℕ → ℂ)
    (R : ℕ → ℕ → ℝ) (r : ℕ → ℝ)
    (hu : ∀ m n, ‖u n-p m n‖ ≤ R m n) (hv : ∀ m, ‖v-q m‖ ≤ r m)
    (hp : ∀ m, Tendsto (p m) atTop (𝓝 (q m)))
    (hR : ∀ m, Tendsto (R m) atTop (𝓝 (r m))) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 v) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨m, hm⟩ := (hr.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < eps/4))).exists
  have hp' := (Metric.tendsto_atTop.mp (hp m)) (eps/4) (by positivity)
  obtain ⟨N1, hN1⟩ := hp'
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp
    ((hR m).eventually (gt_mem_nhds (by linarith : r m < eps/2)))
  refine ⟨max N1 N2, ?_⟩
  intro n hn
  have h1 := hN1 n ((le_max_left _ _).trans hn)
  have h2 := hN2 n ((le_max_right _ _).trans hn)
  have htri := norm_sub_le_norm_sub_add_norm_sub (u n) (p m n) v
  have htri' := norm_sub_le_norm_sub_add_norm_sub (p m n) (q m) v
  rw [dist_eq_norm] at h1 ⊢
  have hlast : ‖q m-v‖ ≤ r m := by rw [norm_sub_rev]; exact hv m
  have hfirst := hu m n
  linarith

end Luce.Section6
