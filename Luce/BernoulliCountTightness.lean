import Luce.UncappedPoisson

/-!
# Eventual tightness of finite Bernoulli row counts

Total predictable mass converging in probability is enough for count
tightness after predictable deletion. No bound on the expectation of the
original row's total predictable mass is assumed. The maximum condition
ensures that the fixed individual-probability cap deletes terms only on
an event of probability tending to zero.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Luce.BernoulliProcess

section OneRow

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (X : BernoulliProcess P)

/-- Markov's inequality for the observed count, using the predictable
compensator identity and a deterministic cap on that compensator. -/
theorem count_tail_le_of_sum_probability_le (N : ℕ) {K R : ℝ} (hR : 0 < R)
    (hK : ∀ ω, ∑ k ∈ Finset.range N, X.probability k ω ≤ K) :
    P.real {ω | R < ∑ k ∈ Finset.range N, X.observation k ω} ≤ K / R := by
  have hI : Integrable (fun ω => ∑ k ∈ Finset.range N, X.observation k ω) P :=
    integrable_finsetSum _ (fun k _ => X.integrable_observation k)
  have hp : Integrable (fun ω => ∑ k ∈ Finset.range N, X.probability k ω) P :=
    integrable_finsetSum _ (fun k _ => X.integrable_probability k)
  have hE : (∫ ω, ∑ k ∈ Finset.range N, X.observation k ω ∂P) ≤ K := by
    rw [X.integral_sum_observation]
    calc
      (∫ ω, ∑ k ∈ Finset.range N, X.probability k ω ∂P) ≤ ∫ _ω : Ω, K ∂P :=
        integral_mono hp (integrable_const K) hK
      _ = K := by simp
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all P (fun ω => Finset.sum_nonneg
      (fun k _ => X.observation_nonneg k ω))) hI R
  have hset : P.real {ω | R < ∑ k ∈ Finset.range N, X.observation k ω} ≤
      P.real {ω | R ≤ ∑ k ∈ Finset.range N, X.observation k ω} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change R ≤ ∑ k ∈ Finset.range N, X.observation k ω
    exact le_of_lt hω
  apply (le_div_iff₀ hR).mpr
  simpa only [mul_comm] using
    ((mul_le_mul_of_nonneg_left hset hR.le).trans hMarkov).trans hE

end OneRow

section Rows

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]

/-- Both fixed-cap failure events have asymptotically vanishing probability. -/
theorem row_bad_event_tendsto_zero (X : ∀ n, BernoulliProcess (P n)) (N : ℕ → ℕ)
    {c δ K : ℝ} (hδ : 0 < δ) (hcK : c < K)
    (htotal : ConvergesInProbability P
      (fun n ω => ∑ k ∈ Finset.range (N n), (X n).probability k ω) c)
    (hmax : ConvergesInProbability P (fun n => (X n).rowMaximum (N n)) 0) :
    Tendsto (fun n => (P n).real
      ({ω | δ < (X n).rowMaximum (N n) ω} ∪
        {ω | K < ∑ k ∈ Finset.range (N n), (X n).probability k ω}))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => measureReal_union_le _ _)
  simpa only [zero_add] using (hmax.upper_tail hδ).add (htotal.upper_tail hcK)

/-- The finite observation counts are eventually tight under convergence
of the total predictable mass and vanishing maximum individual probability.
The bound is eventual in the row index; no uniform claim for all rows or
expectation bound on the original counts is assumed. -/
theorem count_tightness_rows (X : ∀ n, BernoulliProcess (P n)) (N : ℕ → ℕ)
    {c : ℝ} (hc : 0 ≤ c)
    (htotal : ConvergesInProbability P
      (fun n ω => ∑ k ∈ Finset.range (N n), (X n).probability k ω) c)
    (hmax : ConvergesInProbability P (fun n => (X n).rowMaximum (N n)) 0) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ᶠ n in atTop,
      (P n).real {ω | (M : ℝ) < ∑ k ∈ Finset.range (N n), (X n).observation k ω} < ε := by
  intro ε hε
  let K : ℝ := c + 2
  have hK0 : 0 ≤ K := by dsimp [K]; linarith
  have hcK : c < K := by dsimp [K]; linarith
  let Y : ∀ n, BernoulliProcess (P n) :=
    fun n => ((X n).truncateAt (N n)).stop (1 / 2) K
  let bad : ∀ n, Set (Ω n) := fun n =>
    {ω | (1 / 2 : ℝ) < (X n).rowMaximum (N n) ω} ∪
      {ω | K < ∑ k ∈ Finset.range (N n), (X n).probability k ω}
  have hbad : Tendsto (fun n => (P n).real (bad n)) atTop (𝓝 0) :=
    row_bad_event_tendsto_zero P X N (by norm_num) hcK htotal hmax
  obtain ⟨M, hM⟩ := exists_nat_gt (max (0 : ℝ) (K / (ε / 2)))
  have hM0 : (0 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hKM : K / (M : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hM0).mpr
    have h := (div_lt_iff₀ (half_pos hε)).mp ((le_max_right _ _).trans_lt hM)
    simpa only [mul_comm] using h
  refine ⟨M, ?_⟩
  have hsmall : ∀ᶠ n in atTop, (P n).real (bad n) < ε / 2 :=
    hbad.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hsmall] with n hn
  have hinc :
      {ω | (M : ℝ) < ∑ k ∈ Finset.range (N n), (X n).observation k ω} ⊆
        {ω | (M : ℝ) < ∑ k ∈ Finset.range (N n), (Y n).observation k ω} ∪ bad n := by
    intro ω hω
    by_cases hb : ω ∈ bad n
    · exact Or.inr hb
    · apply Or.inl
      have hgood := hb
      simp only [bad, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hgood
      have heq : (∑ k ∈ Finset.range (N n), (Y n).observation k ω) =
          ∑ k ∈ Finset.range (N n), (X n).observation k ω := by
        apply Finset.sum_congr rfl
        intro k hk
        exact ((X n).truncatedStop_eq_on_good ω hgood.1 hgood.2
          (Finset.mem_range.mp hk)).1
      change (M : ℝ) < _
      rwa [heq]
  calc
    (P n).real {ω | (M : ℝ) < ∑ k ∈ Finset.range (N n), (X n).observation k ω} ≤
        (P n).real ({ω | (M : ℝ) < ∑ k ∈ Finset.range (N n), (Y n).observation k ω} ∪ bad n) :=
      measureReal_mono hinc (measure_ne_top _ _)
    _ ≤ (P n).real {ω | (M : ℝ) < ∑ k ∈ Finset.range (N n), (Y n).observation k ω} +
        (P n).real (bad n) := measureReal_union_le _ _
    _ ≤ K / (M : ℝ) + (P n).real (bad n) := by
      exact add_le_add ((Y n).count_tail_le_of_sum_probability_le (N n) hM0
        (fun ω => ((X n).truncateAt (N n)).stop_sum_probability_le_cap hK0 (N n) ω)) le_rfl
    _ < ε := by linarith

end Rows
end Luce.BernoulliProcess
