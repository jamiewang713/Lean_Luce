import Luce.Section1Assumptions
import Luce.Section4EndpointAsymptotic

/-!
# The endpoint estimate from the approved assumptions

This file connects the manuscript's normalization and endpoint assumption to
the epsilon expectation estimate.  Shrinking the terminal neighborhood is
internal to the proof; no additional hypothesis is imposed on the array.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Luce

lemma NormalizedWeights.sum_rates_succ {w : WeightArray} (hnorm : NormalizedWeights w)
    (n : ℕ) : ∑ i, (w (n + 1)).rate i = ((n + 1 : ℕ) : ℝ) := by
  have h := hnorm (n + 1) (Nat.succ_pos n)
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hdiv : (∑ i, (w (n + 1)).rate i) / ((n + 1 : ℕ) : ℝ) = 1 := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h
  simpa only [one_mul] using (div_eq_iff hn).mp hdiv

/-- The approved endpoint assumption supplies the rates required for the
rounded terminal counts in the existing epsilon estimate. -/
lemma EndpointAssumption.eventually_terminal_rates {w : WeightArray}
    (hend : EndpointAssumption w) :
    ∃ γ ε₀ : ℝ, 0 < γ ∧ 0 < ε₀ ∧
      ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 ⌈ε₀ * (n + 1)⌉₊,
        γ ≤ (w (n + 1)).rate (terminalCandidate n m) := by
  obtain ⟨γ, ε₀, n₀, hγ, hε₀, hrate⟩ := hend
  let ε₁ : ℝ := min ε₀ (1 / 2)
  have hε₁ : 0 < ε₁ := lt_min hε₀ (by norm_num)
  have hε₁ε₀ : ε₁ ≤ ε₀ := min_le_left _ _
  have hε₁one : ε₁ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  refine ⟨γ, ε₁, hγ, hε₁, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  intro m hm
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hceil_le : ⌈ε₁ * (n + 1)⌉₊ ≤ n + 1 := by
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_add, Nat.cast_one] using
      mul_le_of_le_one_left hN.le hε₁one
  have hmn : m ≤ n + 1 := (Finset.mem_Icc.mp hm).2.trans hceil_le
  have hindex : ((terminalCandidate n m).val : ℝ) + (m : ℝ) = (n : ℝ) + 1 := by
    exact_mod_cast terminalCandidate_val_add (Finset.mem_Icc.mp hm).1 hmn
  have hm_lt : (m : ℝ) < ε₁ * (n + 1) + 1 :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans_lt
      (Nat.ceil_lt_add_one (mul_nonneg hε₁.le hN.le))
  apply hrate (n + 1) (hn.trans (Nat.le_succ n)) (terminalCandidate n m)
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith [mul_le_mul_of_nonneg_right hε₁ε₀ hN.le]

/-- Equation `eq:tail-epsilon`, derived from the approved normalization and
endpoint assumption without any profile hypothesis. -/
theorem endpointAssumption_epsilon_estimate (w : WeightArray)
    (hnorm : NormalizedWeights w) (hend : EndpointAssumption w) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        limsup (epsilonTailExpectation (fun n => w (n + 1)) ε) atTop ≤
          (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4) := by
  obtain ⟨γ, ε₀, hγ, hε₀, hrate⟩ := hend.eventually_terminal_rates
  refine ⟨γ, hγ, ?_⟩
  exact endpoint_epsilon_estimate (fun n => w (n + 1)) hnorm.sum_rates_succ hγ hε₀ hrate

/-- The same epsilon estimate, retaining eventual boundedness of the
expectations. This makes later comparisons of real-valued limsups valid. -/
theorem endpointAssumption_epsilon_estimate_bounded (w : WeightArray)
    (hnorm : NormalizedWeights w) (hend : EndpointAssumption w) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        IsBoundedUnder (· ≤ ·) atTop (epsilonTailExpectation (fun n => w (n + 1)) ε) ∧
        limsup (epsilonTailExpectation (fun n => w (n + 1)) ε) atTop ≤
          (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4) := by
  obtain ⟨γ, ε₀, hγ, hε₀, hrate⟩ := hend.eventually_terminal_rates
  let δ : ℝ := min ε₀ ((min (1 / 4 : ℝ) (Real.exp (-2 / γ) / 2)) ^ 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    apply lt_min hε₀
    positivity
  refine ⟨γ, hγ, δ, hδ, ?_⟩
  intro ε hε hεδ
  have hεε₀ : ε ≤ ε₀ := (hεδ.trans_le (min_le_left _ _)).le
  have hεmin : ε < (min (1 / 4 : ℝ) (Real.exp (-2 / γ) / 2)) ^ 2 :=
    hεδ.trans_le (min_le_right _ _)
  have hminpos : 0 < min (1 / 4 : ℝ) (Real.exp (-2 / γ) / 2) := by positivity
  have hroot : Real.sqrt ε < min (1 / 4 : ℝ) (Real.exp (-2 / γ) / 2) :=
    (Real.sqrt_lt' hminpos).mpr hεmin
  have hrootSmall : Real.sqrt ε < 1 / 4 := hroot.trans_le (min_le_left _ _)
  have hrootpos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hεsmall : ε < 1 / 4 := by
    nlinarith [Real.sqrt_nonneg ε, Real.sq_sqrt hε.le]
  have hgap : 2 * ε < Real.sqrt ε := by
    nlinarith [Real.sq_sqrt hε.le]
  have hrootone : Real.sqrt ε ≤ 1 := by linarith
  have hcutoff : Real.sqrt ε ≤ Real.exp (-2 / γ) / 2 :=
    (hroot.trans_le (min_le_right _ _)).le
  have hrateε : ∀ᶠ n : ℕ in atTop, ∀ m ∈ Finset.Icc 1 ⌈ε * (n + 1)⌉₊,
      γ ≤ (w (n + 1)).rate (terminalCandidate n m) := by
    filter_upwards [hrate] with n hn
    intro m hm
    apply hn m
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
      (Finset.mem_Icc.mp hm).2.trans
        (Nat.ceil_mono (mul_le_mul_of_nonneg_right hεε₀ (by positivity)))⟩
  refine ⟨?_, epsilonTailExpectation_power_limsup (fun n => w (n + 1))
    hnorm.sum_rates_succ hε hεsmall hγ hcutoff hrateε⟩
  have hbound := epsilonTailExpectation_eventually_le (fun n => w (n + 1))
    hnorm.sum_rates_succ hε hγ hgap hrootone hcutoff hrateε
  have hlim := (tendsto_endpoint_early_envelope (ε := ε) hrootpos).add_const
    (2 * (2 * Real.sqrt ε) ^ (γ / 2))
  simp only [zero_add] at hlim
  refine ⟨2 * (2 * Real.sqrt ε) ^ (γ / 2) + 1, ?_⟩
  change ∀ᶠ n in atTop, epsilonTailExpectation (fun n => w (n + 1)) ε n ≤
    2 * (2 * Real.sqrt ε) ^ (γ / 2) + 1
  filter_upwards [hbound, hlim.eventually
    (Iio_mem_nhds (lt_add_one (2 * (2 * Real.sqrt ε) ^ (γ / 2))))] with n hn henv
  exact hn.trans henv.le

end Luce
