import Luce.Section2CappedPoisson
import Luce.Section2ConvergenceInProbability

/-!
# Predictable Poisson limits for triangular arrays

Rows are allowed to live on different probability spaces, as do the finite
exponential races in the manuscript.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Luce
namespace BernoulliProcess

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]

/-- The capped Laplace criterion on the natural varying row spaces. -/
theorem capped_laplace_tendsto_rows (X : ∀ n, BernoulliProcess (μ n))
    (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) {δ K lam : ℝ} (hδ : δ < 1) (hlam : 0 ≤ lam)
    (hg : ∀ n k, 0 ≤ g n k) (a : ∀ n, Ω n → ℝ)
    (hameas : ∀ n, Measurable (a n)) (ha0 : ∀ n ω, 0 ≤ a n ω)
    (haδ : ∀ n ω, a n ω ≤ δ)
    (hp : ∀ n k ω, (X n).probability k ω ≤ a n ω)
    (hK : ∀ n ω, ∑ k ∈ Finset.range (N n), (X n).probability k ω ≤ K)
    (hatendsto : ConvergesInProbability μ a 0)
    (hcomp : ConvergesInProbability μ
      (fun n => (X n).laplaceCompensator (g n) (N n)) lam) :
    Tendsto (fun n => ∫ ω, Real.exp (-(∑ k ∈ Finset.range (N n),
      g n k * (X n).observation k ω)) ∂μ n) atTop (𝓝 (Real.exp (-lam))) := by
  have haint : ∀ n, Integrable (a n) (μ n) := fun n =>
    ⟨(hameas n).aestronglyMeasurable, HasFiniteIntegral.of_mem_Icc 0 δ
      (ae_of_all _ (fun ω => ⟨ha0 n ω, haδ n ω⟩))⟩
  have hta : Tendsto (fun n => ∫ ω, a n ω ∂μ n) atTop (𝓝 0) := by
    have h := hatendsto.integral_abs_tendsto hameas (fun n ω => by
      simpa only [sub_zero, abs_of_nonneg (ha0 n ω)] using haδ n ω)
    simpa only [sub_zero, abs_of_nonneg (ha0 _ _)] using h
  have hSmeas : ∀ n, Measurable ((X n).laplaceCompensator (g n) (N n)) := by
    intro n
    apply Finset.measurable_sum
    intro k _
    exact (((X n).predictable k).mono ((X n).filtration.le k)).measurable.mul_const _
  have htc := hcomp.integral_abs_tendsto hSmeas (B := K + |lam|) (fun n ω => by
    have hb := (X n).laplaceCompensator_bounds (g n) (hg n) (N n) ω
    calc
      |(X n).laplaceCompensator (g n) (N n) ω - lam| ≤
          |(X n).laplaceCompensator (g n) (N n) ω| + |lam| := abs_sub _ _
      _ ≤ K + |lam| := by rw [abs_of_nonneg hb.1]; exact add_le_add (hb.2.trans (hK n ω)) le_rfl)
  let error := fun n => Real.exp (K / (1 - δ)) *
    (K / (1 - δ) * (∫ ω, a n ω ∂μ n) +
      ∫ ω, |(X n).laplaceCompensator (g n) (N n) ω - lam| ∂μ n)
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
    dsimp [error]
    linarith
  · intro n
    have h := (abs_le.mp ((X n).integral_laplace_error_of_atom_bound
      (g n) (hg n) (N n) hδ hlam (haint n) (ha0 n) (haδ n) (hp n) (hK n))).2
    dsimp [error]
    linarith

end BernoulliProcess
end Luce
