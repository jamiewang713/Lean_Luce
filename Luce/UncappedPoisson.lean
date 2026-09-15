import Luce.FiniteBernoulliRow
import Luce.PredictablePoisson

/-!
# Removing the predictable Poisson caps

The scalar Laplace conclusion of `lem:predictable-poisson` follows from
convergence of the total compensator, largest individual coefficient, and
tested compensator. Rows may have different probability spaces and lengths.

The proof follows the manuscript's predictable deletion rule at fixed
`δ = 1/2` and `K = c + 2`, applies the capped likelihood argument, and
removes the deletion on an event whose probability tends to zero.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Luce

private lemma integral_difference_le_bad_probability
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Ω → ℝ} (hAint : Integrable A μ) (hBint : Integrable B μ)
    (hA : ∀ ω, 0 ≤ A ω ∧ A ω ≤ 1) (hB : ∀ ω, 0 ≤ B ω ∧ B ω ≤ 1)
    (bad : Set Ω) (hbad : MeasurableSet bad) (heq : ∀ ω, ω ∉ bad → A ω = B ω) :
    |(∫ ω, A ω ∂μ) - ∫ ω, B ω ∂μ| ≤ μ.real bad := by
  rw [← integral_sub hAint hBint]
  calc
    |∫ ω, A ω - B ω ∂μ| ≤ ∫ ω, |A ω - B ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, bad.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
      apply integral_mono (hAint.sub hBint).abs ((integrable_const 1).indicator hbad)
      intro ω
      change |A ω - B ω| ≤ bad.indicator (fun _ => (1 : ℝ)) ω
      by_cases hb : ω ∈ bad
      · rw [Set.indicator_of_mem hb, abs_le]
        have ha := hA ω
        have hb' := hB ω
        constructor <;> linarith
      · rw [Set.indicator_of_notMem hb, heq ω hb, sub_self, abs_zero]
    _ = μ.real bad := integral_indicator_one hbad

namespace BernoulliProcess

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]

/-- The finite-row predictable Poisson Laplace limit with no deterministic
cap or assumptions on the original observations after the row ends. -/
theorem uncapped_laplace_tendsto_rows (X : ∀ n, BernoulliProcess (P n))
    (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) {c lam : ℝ}
    (hc : 0 ≤ c) (hlam : 0 ≤ lam) (hg : ∀ n k, 0 ≤ g n k)
    (htotal : ConvergesInProbability P
      (fun n ω => ∑ k ∈ Finset.range (N n), (X n).probability k ω) c)
    (hmax : ConvergesInProbability P (fun n => (X n).rowMaximum (N n)) 0)
    (hcomp : ConvergesInProbability P
      (fun n => (X n).laplaceCompensator (g n) (N n)) lam) :
    Tendsto (fun n => ∫ ω, Real.exp (-(∑ k ∈ Finset.range (N n),
      g n k * (X n).observation k ω)) ∂P n) atTop (𝓝 (Real.exp (-lam))) := by
  let K : ℝ := c + 2
  have hK0 : 0 ≤ K := by dsimp [K]; linarith
  have hcK : c < K := by dsimp [K]; linarith
  let Y : ∀ n, BernoulliProcess (P n) :=
    fun n => ((X n).truncateAt (N n)).stop (1 / 2) K
  let bad : ∀ n, Set (Ω n) := fun n =>
    {ω | (1 / 2 : ℝ) < (X n).rowMaximum (N n) ω} ∪
      {ω | K < ∑ k ∈ Finset.range (N n), (X n).probability k ω}
  have hbadmeas (n : ℕ) : MeasurableSet (bad n) := by
    apply MeasurableSet.union
    · exact measurableSet_lt measurable_const ((X n).measurable_rowMaximum (N n))
    · apply measurableSet_lt measurable_const
      apply Finset.measurable_sum
      intro k _
      exact (((X n).predictable k).mono ((X n).filtration.le k)).measurable
  have hbad : Tendsto (fun n => (P n).real (bad n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => measureReal_union_le _ _)
    simpa only [zero_add] using
      (hmax.upper_tail (by norm_num : (0 : ℝ) < 1 / 2)).add (htotal.upper_tail hcK)
  have heq (n : ℕ) (ω : Ω n) (hω : ω ∉ bad n) (k : ℕ) (hk : k < N n) :
      (Y n).observation k ω = (X n).observation k ω ∧
        (Y n).probability k ω = (X n).probability k ω := by
    simp only [bad, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hω
    exact (X n).truncatedStop_eq_on_good ω hω.1 hω.2 hk
  let a : ∀ n, Ω n → ℝ := fun n ω => min (1 / 2) ((X n).rowMaximum (N n) ω)
  have hameas (n : ℕ) : Measurable (a n) :=
    measurable_const.min ((X n).measurable_rowMaximum (N n))
  have ha0 (n : ℕ) (ω : Ω n) : 0 ≤ a n ω :=
    le_min (by norm_num) ((X n).rowMaximum_nonneg (N n) ω)
  have haδ (n : ℕ) (ω : Ω n) : a n ω ≤ (1 / 2 : ℝ) := min_le_left _ _
  have hp (n k : ℕ) (ω : Ω n) : (Y n).probability k ω ≤ a n ω := by
    apply le_min
    · exact ((X n).truncateAt (N n)).stop_probability_le_cap (by norm_num) k ω
    · have hle : (Y n).probability k ω ≤ ((X n).truncateAt (N n)).probability k ω :=
        stoppedProbability_le (((X n).truncateAt (N n)).probability_nonneg k ω)
      exact hle.trans ((X n).truncateAt_probability_le_rowMaximum (N n) k ω)
  have hatendsto : ConvergesInProbability P a 0 := by
    apply hmax.mono
    intro n ω
    simp only [sub_zero, abs_of_nonneg (ha0 n ω),
      abs_of_nonneg ((X n).rowMaximum_nonneg (N n) ω)]
    exact min_le_right _ _
  have hYcomp : ConvergesInProbability P
      (fun n => (Y n).laplaceCompensator (g n) (N n)) lam := by
    apply hcomp.congr_off bad hbad
    intro n ω hω
    apply Finset.sum_congr rfl
    intro k hk
    rw [(heq n ω hω k (Finset.mem_range.mp hk)).2]
  have hYlimit := capped_laplace_tendsto_rows P Y g N (by norm_num : (1 / 2 : ℝ) < 1)
    hlam hg a hameas ha0 haδ hp
    (fun n ω => ((X n).truncateAt (N n)).stop_sum_probability_le_cap hK0 (N n) ω)
    hatendsto hYcomp
  change Tendsto (fun n => ∫ ω, (Y n).laplaceRow (g n) (N n) ω ∂P n)
    atTop (𝓝 (Real.exp (-lam))) at hYlimit
  have hlapEq (n : ℕ) (ω : Ω n) (hω : ω ∉ bad n) :
      (X n).laplaceRow (g n) (N n) ω = (Y n).laplaceRow (g n) (N n) ω := by
    unfold laplaceRow
    congr 2
    apply Finset.sum_congr rfl
    intro k hk
    rw [(heq n ω hω k (Finset.mem_range.mp hk)).1]
  have hdiff (n : ℕ) :
      |(∫ ω, (X n).laplaceRow (g n) (N n) ω ∂P n) -
        ∫ ω, (Y n).laplaceRow (g n) (N n) ω ∂P n| ≤ (P n).real (bad n) :=
    integral_difference_le_bad_probability
      ((X n).integrable_laplaceRow (g n) (hg n) (N n))
      ((Y n).integrable_laplaceRow (g n) (hg n) (N n))
      ((X n).laplaceRow_bounds (g n) (hg n) (N n))
      ((Y n).laplaceRow_bounds (g n) (hg n) (N n))
      (bad n) (hbadmeas n) (hlapEq n)
  have hdiffzero : Tendsto (fun n =>
      (∫ ω, (X n).laplaceRow (g n) (N n) ω ∂P n) -
        ∫ ω, (Y n).laplaceRow (g n) (N n) ω ∂P n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by
      simpa only [Real.norm_eq_abs] using hdiff n) hbad
  simpa only [sub_add_cancel, zero_add, laplaceRow] using hdiffzero.add hYlimit

end BernoulliProcess
end Luce
