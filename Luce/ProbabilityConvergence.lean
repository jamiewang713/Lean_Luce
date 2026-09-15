import Luce.Predictable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded convergence in probability

The expectation-passage and removal-of-stopping arguments needed for the
predictable Poisson criterion, stated for actual measures and integrals.
-/

open MeasureTheory Filter
open scoped Topology

namespace Luce

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Uniformly bounded random variables converging in probability to a constant
converge in `L¹` to that constant. -/
theorem tendsto_integral_abs_of_bounded_inMeasure {A : ℕ → Ω → ℝ} {c B : ℝ}
    (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, |A n ω| ≤ B)
    (hconv : TendstoInMeasure μ A atTop (fun _ => c)) :
    Tendsto (fun n => ∫ ω, |A n ω - c| ∂μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms⟩ := TendstoInMeasure.exists_seq_tendsto_ae
    (fun ε hε => (hconv ε hε).comp hns)
  refine ⟨ms, ?_⟩
  have hdom : ∀ n, ∀ᵐ ω ∂μ, ‖|A (ns (ms n)) ω - c|‖ ≤ B + |c| := by
    intro n
    filter_upwards [hbound (ns (ms n))] with ω hω
    simp only [Real.norm_eq_abs, abs_abs]
    exact (abs_sub _ _).trans (add_le_add hω le_rfl)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => |A (ns (ms n)) ω - c|) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hms] with ω hω
    simpa using (hω.sub (tendsto_const_nhds (x := c))).abs
  have h := tendsto_integral_of_dominated_convergence (fun _ : Ω => B + |c|)
    (fun n => ((hA (ns (ms n))).sub aestronglyMeasurable_const).norm)
    (integrable_const _) hdom hlim
  simpa only [Pi.sub_apply, Real.norm_eq_abs, integral_zero] using h

/-- A sequence of bounded mean-one likelihoods may multiply the preceding
convergence even when each likelihood depends on the random variable. -/
theorem tendsto_likelihood_integral {L A : ℕ → Ω → ℝ} {c B C : ℝ}
    (hL : ∀ n, Integrable (L n) μ) (hA : ∀ n, Integrable (A n) μ)
    (hmean : ∀ n, (∫ ω, L n ω ∂μ) = 1)
    (hL0 : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ L n ω)
    (hLC : ∀ n, ∀ᵐ ω ∂μ, L n ω ≤ C)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, |A n ω| ≤ B)
    (hconv : TendstoInMeasure μ A atTop (fun _ => c)) :
    Tendsto (fun n => ∫ ω, L n ω * A n ω ∂μ) atTop (𝓝 c) := by
  have hL1 := tendsto_integral_abs_of_bounded_inMeasure
    (fun n => (hA n).aestronglyMeasurable) hbound hconv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => c - C * ∫ ω, |A n ω - c| ∂μ)
    (h := fun n => c + C * ∫ ω, |A n ω - c| ∂μ)
  · simpa using tendsto_const_nhds.sub (hL1.const_mul C)
  · simpa using tendsto_const_nhds.add (hL1.const_mul C)
  · intro n
    have h := (abs_le.mp (likelihood_integral_error (c := c) (hL n) (hA n)
      (hmean n) (hL0 n) (hLC n))).1
    linarith
  · intro n
    have h := (abs_le.mp (likelihood_integral_error (c := c) (hL n) (hA n)
      (hmean n) (hL0 n) (hLC n))).2
    linarith

/-- The elementary bounded-convergence estimate, also valid when the
probability space changes from one row to the next. -/
theorem integral_abs_le_threshold_add_probability {A : Ω → ℝ} {c B ε : ℝ}
    (hA : Measurable A) (hbound : ∀ ω, |A ω - c| ≤ B) (hε : 0 ≤ ε) :
    (∫ ω, |A ω - c| ∂μ) ≤ ε + B * μ.real {ω | ε < |A ω - c|} := by
  classical
  let s : Set Ω := {ω | ε < |A ω - c|}
  have hs : MeasurableSet s := measurableSet_lt measurable_const ((hA.sub_const c).norm)
  have hint : Integrable (fun ω => |A ω - c|) μ :=
    ⟨(hA.sub_const c).norm.aestronglyMeasurable,
      HasFiniteIntegral.of_mem_Icc 0 B (ae_of_all _ (fun ω => ⟨abs_nonneg _, hbound ω⟩))⟩
  have henv : Integrable (fun ω => ε + s.indicator (fun _ => B) ω) μ :=
    (integrable_const ε).add ((integrable_const B).indicator hs)
  calc
    (∫ ω, |A ω - c| ∂μ) ≤ ∫ ω, ε + s.indicator (fun _ => B) ω ∂μ := by
      apply integral_mono_ae hint henv
      apply ae_of_all
      intro ω
      change |A ω - c| ≤ ε + s.indicator (fun _ => B) ω
      by_cases h : ω ∈ s
      · rw [Set.indicator_of_mem h]
        linarith [hbound ω]
      · rw [Set.indicator_of_notMem h, add_zero]
        exact le_of_not_gt h
    _ = _ := by
      rw [integral_add (integrable_const ε) ((integrable_const B).indicator hs),
        integral_indicator hs]
      simp [s, measureReal_def, mul_comm]

/-- Bounded convergence in probability for triangular arrays on different
probability spaces, in the real-valued tail-probability formulation. -/
theorem tendsto_integral_abs_of_bounded_probability
    {Ω' : ℕ → Type*} [∀ n, MeasurableSpace (Ω' n)] (μ' : ∀ n, Measure (Ω' n))
    [∀ n, IsProbabilityMeasure (μ' n)] (A : ∀ n, Ω' n → ℝ) {c B : ℝ}
    (hA : ∀ n, Measurable (A n)) (hbound : ∀ n ω, |A n ω - c| ≤ B)
    (hconv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ' n).real {ω | ε < |A n ω - c|}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |A n ω - c| ∂μ' n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht := (hconv (ε / 2) (half_pos hε)).const_mul B
  have hev : ∀ᶠ n in atTop, B * (μ' n).real {ω | ε / 2 < |A n ω - c|} < ε / 2 :=
    ht.eventually (gt_mem_nhds (by simpa using half_pos hε))
  filter_upwards [hev] with n hn
  have hb := integral_abs_le_threshold_add_probability (μ := μ' n) (hA n) (hbound n)
    (half_pos hε).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
  linarith

end Luce
