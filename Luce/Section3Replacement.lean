import Luce.Section3Compensator
import Luce.ConvergenceInProbability

/-!
# Probability form of the interior survival replacement

This completes the fixed-positive-cutoff stochastic argument of
`fixed_points.tex`, lines 759–780. The quantile convergence and deterministic
cutoff bounds are exposed as auxiliary hypotheses; no final Section 3
statement is claimed by this module.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- Markov's inequality with an exceptional event. The error itself need
not be measurable because the estimate uses outer probability. -/
lemma probability_error_le_bad_add_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (bad : Set Ω)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hY : Integrable Y μ)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hbound : ∀ ω, ω ∉ bad → |X ω| ≤ C * Y ω) :
    μ.real {ω | ε < |X ω|} ≤ μ.real bad + (C / ε) * ∫ ω, Y ω ∂μ := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => C * Y ω)
    (Eventually.of_forall fun ω => mul_nonneg hC (hY0 ω)) (hY.const_mul C) ε
  rw [integral_const_mul] at hm
  have hm' : μ.real {ω | ε ≤ C * Y ω} ≤ (C / ε) * ∫ ω, Y ω ∂μ := by
    calc
      _ ≤ (C * ∫ ω, Y ω ∂μ) / ε := (le_div_iff₀ hε).mpr (by linarith)
      _ = _ := by ring
  calc
    _ ≤ μ.real (bad ∪ {ω | ε ≤ C * Y ω}) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      by_cases hb : ω ∈ bad
      · exact Or.inl hb
      · exact Or.inr (hω.le.trans (hbound ω hb))
    _ ≤ μ.real bad + μ.real {ω | ε ≤ C * Y ω} := measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl hm'

lemma integrable_normalized_clockBand {n : ℕ} (w : Weights (n + 1))
    (s : Finset (Fin (n + 1))) (t : Fin (n + 1) → ℝ) (δ : ℝ) :
    Integrable (fun E =>
      (∑ i ∈ s, w.rate i * clockBand (t i) δ (E i)) / (n + 1 : ℕ))
      (exponentialRace w) := by
  apply Integrable.div_const
  apply integrable_finsetSum
  intro i _
  exact ((memLp_of_bounded (μ := exponentialRace w)
    (Eventually.of_forall fun E : Fin (n + 1) → ℝ => clockBand_mem_Icc (t i) δ (E i))
    ((measurable_clockBand (t i) δ).comp (measurable_pi_apply i)).aestronglyMeasurable
    2).integrable (by norm_num)).const_mul _

/-- A quantitative version of the replacement argument: the error
probability is bounded by the quantile error probability plus a constant
times the band width. The estimates are uniform in n and in all rates. -/
theorem probability_survival_replacement_le {n : ℕ} (w : Weights (n + 1))
    (s : Finset (Fin (n + 1))) (c t : Fin (n + 1) → ℝ)
    (τ : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) {C u δ ε : ℝ}
    (hC : 0 ≤ C) (hc : ∀ i ∈ s, |c i| ≤ C) (hu : 0 < u)
    (ht : ∀ i ∈ s, u ≤ t i) (hδ : 0 ≤ δ) (hδu : δ ≤ u / 2) (hε : 0 < ε) :
    (exponentialRace w).real {E | ε <
      |((∑ i ∈ s, c i * w.rate i * survivalGe (τ E i) (E i)) -
        (∑ i ∈ s, c i * w.rate i * survivalGe (t i) (E i))) / (n + 1 : ℕ)|} ≤
      (exponentialRace w).real {E | ∃ i ∈ s, δ < |τ E i - t i|} +
        (C / ε) * (8 * δ / (u / 2) ^ 2) := by
  let Y := fun E : Fin (n + 1) → ℝ =>
    (∑ i ∈ s, w.rate i * clockBand (t i) δ (E i)) / (n + 1 : ℕ)
  have hY0 : ∀ E, 0 ≤ Y E := by
    intro E
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (w.positive i).le (clockBand_mem_Icc (t i) δ (E i)).1
  have hb := probability_error_le_bad_add_integral (exponentialRace w)
    (fun E => ((∑ i ∈ s, c i * w.rate i * survivalGe (τ E i) (E i)) -
      (∑ i ∈ s, c i * w.rate i * survivalGe (t i) (E i))) / (n + 1 : ℕ))
    Y {E | ∃ i ∈ s, δ < |τ E i - t i|} hC hε
    (integrable_normalized_clockBand w s t δ) hY0 ?_
  · apply hb.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hC hε.le)
    exact integral_normalized_clockBand_le w s t hδ (half_pos hu)
      (fun i hi => by linarith [ht i hi])
  · intro E hE
    have hclose : ∀ i ∈ s, |τ E i - t i| ≤ δ := by
      intro i hi
      exact le_of_not_gt (fun h => hE ⟨i, hi, h⟩)
    have h := survival_replacement_bound s w.rate c (τ E) t E
      (fun i _ => (w.positive i).le) hc hclose
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n + 1 : ℕ) by positivity)]
    have h' := div_le_div_of_nonneg_right h (show (0 : ℝ) ≤ (n + 1 : ℕ) by positivity)
    simpa only [Y, clockBand, mul_div_assoc] using h'

/-- The full stochastic replacement step on any fixed positive cutoff.
Quantile convergence is supplied explicitly; the shrinking-band probability
bound is proved from the actual exponential law above. -/
theorem survival_replacement_converges
    (w : ∀ n, Weights (n + 1)) (s : ∀ n, Finset (Fin (n + 1)))
    (c t : ∀ n, Fin (n + 1) → ℝ)
    (τ : ∀ n, (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) {C u : ℝ}
    (hC : 0 ≤ C) (hc : ∀ n i, i ∈ s n → |c n i| ≤ C)
    (hu : 0 < u) (ht : ∀ n i, i ∈ s n → u ≤ t n i)
    (hquantile : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => (exponentialRace (w n)).real
      {E | ∃ i ∈ s n, δ < |τ n E i - t n i|}) atTop (𝓝 0)) :
    ConvergesInProbability (fun n => exponentialRace (w n))
      (fun n E =>
        ((∑ i ∈ s n, c n i * (w n).rate i * survivalGe (τ n E i) (E i)) -
          (∑ i ∈ s n, c n i * (w n).rate i * survivalGe (t n i) (E i))) /
            (n + 1 : ℕ)) 0 := by
  intro ε hε
  apply Metric.tendsto_nhds.mpr
  intro q hq
  let K := (C / ε) * (8 / (u / 2) ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨δ₀, hδ₀, hsmall⟩ := exists_pos_mul_lt (half_pos hq) K
  let δ := min δ₀ (u / 2)
  have hδ : 0 < δ := lt_min hδ₀ (half_pos hu)
  have hsmall' : K * δ < q / 2 :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hK).trans_lt hsmall
  filter_upwards [(hquantile δ hδ).eventually (gt_mem_nhds (half_pos hq))] with n hn
  have hbound := probability_survival_replacement_le (w n) (s n) (c n) (t n) (τ n)
    hC (hc n) hu (ht n) hδ.le (min_le_right _ _) hε
  have halg : (C / ε) * (8 * δ / (u / 2) ^ 2) = K * δ := by dsimp [K]; ring
  rw [halg] at hbound
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  simp only [sub_zero]
  linarith

/-- The deterministic-time sum is asymptotic in probability to its exact
expectation on a fixed positive cutoff (lines 776–780). -/
theorem deterministic_survival_fluctuation_converges
    (w : ∀ n, Weights (n + 1)) (s : ∀ n, Finset (Fin (n + 1)))
    (c t : ∀ n, Fin (n + 1) → ℝ) {C u : ℝ}
    (hc : ∀ n i, i ∈ s n → |c n i| ≤ C)
    (hu : 0 < u) (ht : ∀ n i, i ∈ s n → u ≤ t n i) :
    ConvergesInProbability (fun n => exponentialRace (w n))
      (fun n E =>
        (∑ i ∈ s n, c n i * (w n).rate i * survivalGe (t n i) (E i)) /
            (n + 1 : ℕ) -
          (∑ i ∈ s n, c n i * rateKernel (t n i) ((w n).rate i)) / (n + 1 : ℕ)) 0 := by
  let X := fun n (E : Fin (n + 1) → ℝ) =>
    (∑ i ∈ s n, c n i * (w n).rate i * survivalGe (t n i) (E i)) / (n + 1 : ℕ)
  have hX : ∀ n, MemLp (X n) 2 (exponentialRace (w n)) := by
    intro n
    have hsum : MemLp (fun E : Fin (n + 1) → ℝ =>
        ∑ i ∈ s n, c n i * (w n).rate i * survivalGe (t n i) (E i)) 2
        (exponentialRace (w n)) := by
      exact memLp_finsetSum _ (fun i _ => memLp_weighted_survivalGe (w n) i (c n i) (t n i))
    simpa [X, div_eq_mul_inv] using hsum.mul_const (((n + 1 : ℕ) : ℝ)⁻¹)
  have hmean (n : ℕ) : (∫ E, X n E ∂exponentialRace (w n)) =
      (∑ i ∈ s n, c n i * rateKernel (t n i) ((w n).rate i)) / (n + 1 : ℕ) :=
    integral_normalized_survivalGe (w n) (s n) (c n) (t n)
      (fun i hi => hu.le.trans (ht n i hi))
  intro ε hε
  have hlim : Tendsto (fun n => ((4 * C ^ 2 / u ^ 2) / (n + 1 : ℕ)) / ε ^ 2)
      atTop (𝓝 0) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (4 * C ^ 2 / u ^ 2)).div_const (ε ^ 2)
    simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using h
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hlim
  intro n
  have hcheb := meas_ge_le_variance_div_sq (hX n) hε
  have hp : (exponentialRace (w n)) {E | ε < |X n E - ∫ E, X n E ∂exponentialRace (w n)|} ≤
      ENNReal.ofReal (variance (X n) (exponentialRace (w n)) / ε ^ 2) := by
    apply (measure_mono _).trans hcheb
    intro E hE
    exact (show ε < |X n E - ∫ E, X n E ∂exponentialRace (w n)| from hE).le
  have hpr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg ε))] at hpr
  have hv := variance_normalized_survivalGe_le (w n) (s n) (c n) (t n) (hc n) hu (ht n)
  have hfinal := hpr.trans (div_le_div_of_nonneg_right hv (sq_nonneg ε))
  simpa only [sub_zero, hmean n, X, measureReal_def] using hfinal

end Luce
