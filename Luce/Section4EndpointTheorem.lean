import Luce.Section4EndpointRace
import Luce.Section4EndpointCutoff
import Luce.Section4RankProbability

/-! # The finite endpoint proposition

This file proves the two explicit inequalities of Proposition
`prop:endpoint-bound` for the actual independent exponential race. Terminal
labels use the paper's index `m = 1, …, M`; their zero-based label has value
`n + 1 - m` in a race with `n + 1` clocks.
-/

open scoped BigOperators
open Real Set MeasureTheory

namespace Luce

noncomputable section

lemma measurable_raceRank {n : ℕ} (i : Fin n) :
    Measurable (fun clocks : Fin n → ℝ => raceRank clocks i) := by
  classical
  unfold raceRank
  simp only [Finset.card_filter]
  apply measurable_const.add
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.ite
    (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)) measurable_const

/-- Count of fixed points among the selected terminal labels. -/
def terminalFixedPointCount {n : ℕ} (candidate : ℕ → Fin n) (M : ℕ)
    (clocks : Fin n → ℝ) : ℕ :=
  ((Finset.Icc 1 M).filter fun m => raceRank clocks (candidate m) = (candidate m).val + 1).card

lemma integral_terminalFixedPointCount {n : ℕ} (w : Weights n)
    (candidate : ℕ → Fin n) (M : ℕ) :
    (∫ clocks, (terminalFixedPointCount candidate M clocks : ℝ) ∂exponentialRace w) =
      ∑ m ∈ Finset.Icc 1 M,
        (exponentialRace w).real {clocks | raceRank clocks (candidate m) = (candidate m).val + 1} := by
  classical
  let event (m : ℕ) :=
    {clocks : Fin n → ℝ | raceRank clocks (candidate m) = (candidate m).val + 1}
  have hmeas (m : ℕ) : MeasurableSet (event m) :=
    (measurable_raceRank (candidate m)) (measurableSet_singleton _)
  have hint (m : ℕ) : Integrable ((event m).indicator (fun _ => (1 : ℝ))) (exponentialRace w) :=
    (integrable_const _).indicator (hmeas m)
  have hcount : (fun clocks => (terminalFixedPointCount candidate M clocks : ℝ)) =
      (fun clocks => ∑ m ∈ Finset.Icc 1 M, (event m).indicator (fun _ => (1 : ℝ)) clocks) := by
    funext clocks
    simp only [terminalFixedPointCount, Finset.card_filter, Nat.cast_sum, event,
      Set.indicator_apply, Set.mem_ofPred_eq]
    apply Finset.sum_congr rfl
    intro m hm
    split_ifs <;> simp
  rw [hcount, integral_finsetSum _ (fun m _ => hint m)]
  apply Finset.sum_congr rfl
  intro m hm
  simpa using integral_indicator_const (μ := exponentialRace w) (1 : ℝ) (hmeas m)

/-- The first explicit inequality in Proposition `prop:endpoint-bound`.
All probabilities, independence and rank conditioning are discharged in the
finite exponential-clock model. The positive universal Chernoff constant is
`(1/2 - exp(-1))/2`. -/
theorem endpoint_fixedPoint_probability_bound {n : ℕ} (w : Weights (n + 1))
    (candidate : ℕ → Fin (n + 1)) {M : ℕ} {s B γ : ℝ}
    (hM : 1 ≤ M) (hterminal : ∀ m ∈ Finset.Icc 1 M, (candidate m).val + m = n + 1)
    (hγ : 0 < γ) (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (candidate m))
    (hcut : meanSurvivors w.rate s = B) (hBM : 2 * (M : ℝ) ≤ B - 1)
    (hs : 1 ≤ γ * s) :
    (∑ m ∈ Finset.Icc 1 M,
      (exponentialRace w).real {clocks | raceRank clocks (candidate m) = (candidate m).val + 1}) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) * B) +
        2 * Real.exp (-γ * s) := by
  have heq : (∑ m ∈ Finset.Icc 1 M,
      (exponentialRace w).real {clocks | raceRank clocks (candidate m) = (candidate m).val + 1}) =
      ∑ m ∈ Finset.Icc 1 M, ∫ t : ℝ in Ioi 0,
        w.rate (candidate m) * Real.exp (-w.rate (candidate m) * t) *
          otherSurvivorProbability w (candidate m) (m - 1) t := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmpos := (Finset.mem_Icc.mp hm).1
    have hlabel := hterminal m hm
    have hindex : n - (candidate m).val = m - 1 := by omega
    simpa only [hindex, otherSurvivorProbability] using fixed_point_probability_integral w (candidate m)
  rw [heq]
  exact exponentialRace_endpoint_integrals w candidate hM hγ hrate hcut hBM hs

/-- Proposition `prop:endpoint-bound`, in expectation form. -/
theorem endpoint_fixedPoint_expectation_bound {n : ℕ} (w : Weights (n + 1))
    (candidate : ℕ → Fin (n + 1)) {M : ℕ} {s B γ : ℝ}
    (hM : 1 ≤ M) (hterminal : ∀ m ∈ Finset.Icc 1 M, (candidate m).val + m = n + 1)
    (hγ : 0 < γ) (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (candidate m))
    (hcut : meanSurvivors w.rate s = B) (hBM : 2 * (M : ℝ) ≤ B - 1)
    (hs : 1 ≤ γ * s) :
    (∫ clocks, (terminalFixedPointCount candidate M clocks : ℝ) ∂exponentialRace w) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) * B) +
        2 * Real.exp (-γ * s) := by
  rw [integral_terminalFixedPointCount]
  exact endpoint_fixedPoint_probability_bound w candidate hM hterminal hγ hrate hcut hBM hs

/-- The normalized power bound in the second inequality of
`eq:tail-explicit`. Taking `B = sqrt ((n+1) * M)` gives the paper's expression. -/
theorem endpoint_fixedPoint_expectation_power_bound {n : ℕ} (w : Weights (n + 1))
    (hnorm : ∑ i, w.rate i = ((n + 1 : ℕ) : ℝ))
    (candidate : ℕ → Fin (n + 1)) {M : ℕ} {s B γ : ℝ}
    (hM : 1 ≤ M) (hterminal : ∀ m ∈ Finset.Icc 1 M, (candidate m).val + m = n + 1)
    (hγ : 0 < γ) (hrate : ∀ m ∈ Finset.Icc 1 M, γ ≤ w.rate (candidate m))
    (hcut : meanSurvivors w.rate s = B) (hBM : 2 * (M : ℝ) ≤ B - 1)
    (hs : 1 ≤ γ * s) :
    (∫ clocks, (terminalFixedPointCount candidate M clocks : ℝ) ∂exponentialRace w) ≤
      (M : ℝ) * Real.exp (-(bernoulliLowerTailConstant / 2) * B) +
        2 * (2 * B / (n + 1)) ^ (γ / 2) := by
  apply (endpoint_fixedPoint_expectation_bound w candidate hM hterminal hγ hrate hcut hBM hs).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
    cutoff_exponential_le_rpow (Nat.succ_pos n) w.rate (fun i => (w.positive i).le) hnorm
      (by nlinarith) hcut hγ.le

end

end Luce
