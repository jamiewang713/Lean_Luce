import Luce.Section5SieveSeries

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce

/-- A finite-approximation argument with the row limit taken before the
approximation order. Every premise is discharged for the cycle application
below by its polynomial limits and factorial remainder bounds. -/
theorem tendsto_of_finite_approximation
    (X : ℕ → ℝ) (A E : ℕ → ℕ → ℝ) (a b : ℕ → ℝ) (p : ℝ)
    (hA : ∀ K, Tendsto (A K) atTop (𝓝 (a K)))
    (hE : ∀ K, Tendsto (E K) atTop (𝓝 (b K)))
    (ha : Tendsto a atTop (𝓝 p)) (hb : Tendsto b atTop (𝓝 0))
    (herr : ∀ K n, |A K n-X n| ≤ E K n) : Tendsto X atTop (𝓝 p) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ha' := (Metric.tendsto_nhds.mp ha) (ε/4) (by positivity)
  have hb' : ∀ᶠ K in atTop, b K < ε/4 := hb.eventually (gt_mem_nhds (by positivity))
  obtain ⟨K, hKa, hKb⟩ := (ha'.and hb').exists
  have hrowA := (Metric.tendsto_nhds.mp (hA K)) (ε/4) (by positivity)
  have hrowE : ∀ᶠ n in atTop, E K n < b K+ε/4 :=
    (hE K).eventually (gt_mem_nhds (by linarith))
  filter_upwards [hrowA, hrowE] with n hnA hnE
  rw [Real.dist_eq] at hKa hnA ⊢
  have he := herr K n
  have ht1 := abs_sub_le (X n) (A K n) (a K)
  have ht2 := abs_sub_le (X n) (a K) p
  rw [abs_sub_comm (X n) (A K n)] at ht1
  linarith

/-- Joint bulk point probabilities converge to the independent-Poisson
formula. Only the original normalization/profile assumptions are used. -/
theorem bulk_cycle_point_indicator_limit (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (L : ℕ) (q : Fin L → ℕ) (α : ℝ) (hα : α < 1) :
    Tendsto (fun n => ∫ z,
      (if (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val) = q
        then (1 : ℝ) else 0) ∂exponentialRace (w n)) atTop
      (𝓝 (∏ ell, Real.exp (-bulkCycleTraceIntensity f α ell.val) *
        bulkCycleTraceIntensity f α ell.val ^ q ell / ((q ell).factorial : ℝ))) := by
  classical
  apply tendsto_of_finite_approximation _
    (fun K n => ∫ z, countVectorSieve q K
      (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val)
      ∂exponentialRace (w n))
    (fun K n => ∫ z, countSieveRemainder q K
      (fun ell => Section5.bulkCycleCount (raceRankPermutation z) α ell.val)
      ∂exponentialRace (w n))
    (fun K => ∏ ell, ∑ j : Fin (K+1),
      (-1 : ℝ)^j.val * bulkCycleTraceIntensity f α ell.val ^ (q ell+j.val) /
        (((q ell).factorial : ℝ) * (j.val.factorial : ℝ)))
    (fun K => limitingSieveRemainder q K (fun ell => bulkCycleTraceIntensity f α ell.val))
  · exact fun K => bulk_count_sieve_expectation_limit w f hnorm hf L K q α hα
  · exact fun K => bulk_sieve_remainder_limit w f hnorm hf L K q α hα
  · exact count_vector_sieve_series_limit q _
  · exact limitingSieveRemainder_tendsto_zero q _
  · exact fun K n => bulk_sieve_error_integral_le (w n) L K q α

end Luce
