import Luce.BernoulliProcess
import Luce.ProbabilityConvergence

/-!
# The capped predictable Poisson criterion

The Laplace-functional argument of Section 2 with a deterministic total-mass
cap. The maximum-atom condition is convergence in probability, rather than
a deterministic bound tending to zero. The preceding `stop` construction
supplies the cap without changing the array on its good event.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Luce
namespace BernoulliProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Compensator tested against `1 - exp(-g)`. -/
noncomputable def laplaceCompensator (X : BernoulliProcess μ) (g : ℕ → ℝ)
    (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N, X.probability k ω * (1 - Real.exp (-g k))

lemma laplaceCompensator_integrable (X : BernoulliProcess μ) (g : ℕ → ℝ) (N : ℕ) :
    Integrable (X.laplaceCompensator g N) μ :=
  integrable_finsetSum _ (fun k _ => (X.integrable_probability k).mul_const _)

lemma laplaceCompensator_bounds (X : BernoulliProcess μ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (N : ℕ) (ω : Ω) :
    0 ≤ X.laplaceCompensator g N ω ∧
      X.laplaceCompensator g N ω ≤ ∑ k ∈ Finset.range N, X.probability k ω := by
  refine ⟨Finset.sum_nonneg (fun k _ => ?_), Finset.sum_le_sum (fun k _ => ?_)⟩
  · exact mul_nonneg (X.probability_nonneg k ω)
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg k))))
  · exact mul_le_of_le_one_right (X.probability_nonneg k ω)
      (by linarith [Real.exp_pos (-g k)])

/-- Quantitative Laplace error for an adapted Bernoulli array with capped mass.
The factor `a` may depend on the entire outcome; it bounds the largest atom. -/
theorem integral_laplace_error_of_atom_bound (X : BernoulliProcess μ)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (N : ℕ) {δ K lam : ℝ} {a : Ω → ℝ}
    (hδ : δ < 1) (hlam : 0 ≤ lam) (haint : Integrable a μ)
    (ha0 : ∀ ω, 0 ≤ a ω) (haδ : ∀ ω, a ω ≤ δ)
    (hp : ∀ k ω, X.probability k ω ≤ a ω)
    (hK : ∀ ω, ∑ k ∈ Finset.range N, X.probability k ω ≤ K) :
    |(∫ ω, Real.exp (-(∑ k ∈ Finset.range N, g k * X.observation k ω)) ∂μ) -
      Real.exp (-lam)| ≤ Real.exp (K / (1 - δ)) *
        (K / (1 - δ) * (∫ ω, a ω ∂μ) +
          ∫ ω, |X.laplaceCompensator g N ω - lam| ∂μ) := by
  have hpδ : ∀ k ω, X.probability k ω ≤ δ := fun k ω => (hp k ω).trans (haδ ω)
  have hA := X.laplaceProduct_integrable hδ g hg hpδ N
  have hL := X.likelihood_integrable hδ g hg hpδ N
  have hS := X.laplaceCompensator_integrable g N
  have hbound := likelihood_integral_error (c := Real.exp (-lam)) hL hA
    (X.integral_likelihood hδ g hg hpδ N)
    (ae_of_all _ (fun ω => (X.likelihood_bounds_of_sum_le hδ g hg hpδ N ω (hK ω)).1))
    (ae_of_all _ (fun ω => (X.likelihood_bounds_of_sum_le hδ g hg hpδ N ω (hK ω)).2))
  have heq : (fun ω => X.likelihood g N ω * X.laplaceProduct g N ω) =
      (fun ω => Real.exp (-(∑ k ∈ Finset.range N, g k * X.observation k ω))) := by
    funext ω
    exact X.likelihood_mul_laplaceProduct hδ g hg hpδ N ω
  rw [heq] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    (∫ ω, |X.laplaceProduct g N ω - Real.exp (-lam)| ∂μ) ≤
        ∫ ω, K / (1 - δ) * a ω + |X.laplaceCompensator g N ω - lam| ∂μ := by
      apply integral_mono_ae (hA.sub (integrable_const _)).abs
        ((haint.const_mul _).add (hS.sub (integrable_const _)).abs)
      apply ae_of_all
      intro ω
      apply product_poisson_error_of_atom_bound (Finset.range N)
        (fun k => X.probability k ω * (1 - Real.exp (-g k)))
      · intro k _
        exact mul_nonneg (X.probability_nonneg k ω)
          (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg k))))
      · intro k _
        exact (mul_le_of_le_one_right (X.probability_nonneg k ω)
          (by linarith [Real.exp_pos (-g k)])).trans (hp k ω)
      · exact ha0 ω
      · exact haδ ω
      · exact hδ
      · exact (X.laplaceCompensator_bounds g hg N ω).2.trans (hK ω)
      · exact hlam
    _ = _ := by
      have hr : Integrable (fun ω => |X.laplaceCompensator g N ω - lam|) μ :=
        (hS.sub (integrable_const lam)).abs
      rw [integral_add (haint.const_mul (K / (1 - δ))) hr, integral_const_mul]

/-- The capped predictable Poisson criterion for a single Laplace test.
Applying this to each nonnegative continuous spatial test gives the Laplace
functional asserted in Lemma `lem:predictable-poisson`. -/
theorem capped_laplace_tendsto (X : ℕ → BernoulliProcess μ) (g : ℕ → ℕ → ℝ)
    (N : ℕ → ℕ) {δ K lam : ℝ} (hδ : δ < 1) (hlam : 0 ≤ lam)
    (hg : ∀ n k, 0 ≤ g n k) (a : ℕ → Ω → ℝ)
    (haint : ∀ n, Integrable (a n) μ) (ha0 : ∀ n ω, 0 ≤ a n ω)
    (haδ : ∀ n ω, a n ω ≤ δ)
    (hp : ∀ n k ω, (X n).probability k ω ≤ a n ω)
    (hK : ∀ n ω, ∑ k ∈ Finset.range (N n), (X n).probability k ω ≤ K)
    (hatendsto : TendstoInMeasure μ a atTop (fun _ => 0))
    (hcomp : TendstoInMeasure μ
      (fun n => (X n).laplaceCompensator (g n) (N n)) atTop (fun _ => lam)) :
    Tendsto (fun n => ∫ ω, Real.exp (-(∑ k ∈ Finset.range (N n),
      g n k * (X n).observation k ω)) ∂μ) atTop (𝓝 (Real.exp (-lam))) := by
  have hta : Tendsto (fun n => ∫ ω, a n ω ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_abs_of_bounded_inMeasure (fun n => (haint n).aestronglyMeasurable)
      (fun n => ae_of_all _ (fun ω => by simpa only [abs_of_nonneg (ha0 n ω)] using haδ n ω))
      hatendsto
    simpa only [sub_zero, abs_of_nonneg (ha0 _ _)] using h
  have htc := tendsto_integral_abs_of_bounded_inMeasure
    (fun n => ((X n).laplaceCompensator_integrable (g n) (N n)).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun ω => by
      rw [abs_of_nonneg ((X n).laplaceCompensator_bounds (g n) (hg n) (N n) ω).1]
      exact ((X n).laplaceCompensator_bounds (g n) (hg n) (N n) ω).2.trans (hK n ω))) hcomp
  let error := fun n => Real.exp (K / (1 - δ)) *
    (K / (1 - δ) * (∫ ω, a n ω ∂μ) +
      ∫ ω, |(X n).laplaceCompensator (g n) (N n) ω - lam| ∂μ)
  have he : Tendsto error atTop (𝓝 0) := by
    simpa [error] using ((hta.const_mul (K / (1 - δ))).add htc).const_mul
      (Real.exp (K / (1 - δ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => Real.exp (-lam) - error n)
    (h := fun n => Real.exp (-lam) + error n)
  · simpa using (tendsto_const_nhds (x := Real.exp (-lam))).sub he
  · simpa using (tendsto_const_nhds (x := Real.exp (-lam))).add he
  · intro n
    have h := (abs_le.mp ((X n).integral_laplace_error_of_atom_bound
      (g n) (hg n) (N n) hδ hlam (haint n) (ha0 n) (haδ n) (hp n) (hK n))).1
    change Real.exp (-lam) - error n ≤ _
    dsimp [error]
    linarith
  · intro n
    have h := (abs_le.mp ((X n).integral_laplace_error_of_atom_bound
      (g n) (hg n) (N n) hδ hlam (haint n) (ha0 n) (haδ n) (hp n) (hK n))).2
    dsimp [error]
    linarith

end BernoulliProcess
end Luce
