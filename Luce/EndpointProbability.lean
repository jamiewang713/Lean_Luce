import Luce.Endpoint
import Mathlib.Probability.Moments.Basic

/-! # Probability estimates for Section 4

The deterministic two-candidate observation persists after taking
expectations. A Chernoff estimate for independent Bernoulli variables handles
the early-time part of the endpoint integral.
-/

open scoped BigOperators
open Real Set MeasureTheory ProbabilityTheory

namespace Luce

noncomputable section

/-- The sum of the probabilities of all terminal candidate events is at
most two, for any random survivor set. -/
theorem two_candidate_probability_bound {Ω α : Type*} [MeasurableSpace Ω]
    [DecidableEq α] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (survivors : Ω → Finset α) (candidate : ℕ → α) (M : ℕ)
    (hmeas : ∀ m ∈ Finset.Icc 1 M,
      MeasurableSet {ω | ((survivors ω).erase (candidate m)).card = m - 1}) :
    (∑ m ∈ Finset.Icc 1 M,
      μ.real {ω | ((survivors ω).erase (candidate m)).card = m - 1}) ≤ 2 := by
  classical
  let event (m : ℕ) := {ω | ((survivors ω).erase (candidate m)).card = m - 1}
  have hint : ∀ m ∈ Finset.Icc 1 M,
      Integrable ((event m).indicator (fun _ : Ω => (1 : ℝ))) μ := by
    intro m hm
    exact (integrable_const 1).indicator (hmeas m hm)
  have hsum : (∫ ω, ∑ m ∈ Finset.Icc 1 M,
      (event m).indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) =
      ∑ m ∈ Finset.Icc 1 M, μ.real (event m) := by
    rw [integral_finsetSum _ hint]
    apply Finset.sum_congr rfl
    intro m hm
    simpa using integral_indicator_const (μ := μ) (1 : ℝ) (hmeas m hm)
  rw [← hsum]
  calc
    _ ≤ ∫ _ : Ω, (2 : ℝ) ∂μ := by
      apply integral_mono (integrable_finsetSum _ hint) (integrable_const 2)
      intro ω
      have hc : ((Finset.Icc 1 M).filter fun m =>
          ((survivors ω).erase (candidate m)).card = m - 1).card ≤ 2 :=
        two_candidate_bound_Icc (survivors ω) candidate M
      have hcR : (((Finset.Icc 1 M).filter fun m =>
          ((survivors ω).erase (candidate m)).card = m - 1).card : ℝ) ≤ 2 := by
        exact_mod_cast hc
      simpa [event, Set.indicator, Finset.sum_boole] using hcR
    _ = 2 := by simp

/-- The universal positive constant in the Bernoulli lower-tail estimate. -/
def bernoulliLowerTailConstant : ℝ := 1 / 2 - Real.exp (-1)

theorem bernoulliLowerTailConstant_pos : 0 < bernoulliLowerTailConstant := by
  have he : (2 : ℝ) < Real.exp 1 := by
    simpa only [one_add_one_eq_two] using
      Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
  have hinv : Real.exp (-1) < (1 : ℝ) / 2 := by
    rw [Real.exp_neg, one_div]
    exact inv_strictAnti₀ (by norm_num) he
  exact sub_pos.mpr hinv

/-- A zero-one random variable is integrable on a probability space. -/
theorem integrable_of_zero_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (h01 : ∀ ω, X ω = 0 ∨ X ω = 1) : Integrable X μ := by
  apply (integrable_const (1 : ℝ)).mono' hX.aestronglyMeasurable
  filter_upwards [] with ω
  rcases h01 ω with h | h <;> simp [h]

/-- The Laplace transform of a Bernoulli variable at parameter one. -/
theorem mgf_neg_one_of_zero_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (h01 : ∀ ω, X ω = 0 ∨ X ω = 1) :
    mgf X μ (-1) = 1 - (1 - Real.exp (-1)) * ∫ ω, X ω ∂μ := by
  have hid : (fun ω => Real.exp ((-1) * X ω)) =
      (fun ω => 1 - (1 - Real.exp (-1)) * X ω) := by
    funext ω
    rcases h01 ω with h | h <;> simp [h]
  rw [mgf, hid, integral_sub (integrable_const _)
    ((integrable_of_zero_one μ hX h01).const_mul _), integral_const_mul]
  simp

/-- The multiplicative Chernoff lower-tail estimate for a finite sum of
independent Bernoulli variables. No identical-distribution hypothesis is used. -/
theorem bernoulli_sum_lower_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hind : iIndepFun X μ) (indices : Finset ι) :
    μ.real {ω | (∑ i ∈ indices, X i ω) ≤ (∑ i ∈ indices, ∫ ω, X i ω ∂μ) / 2} ≤
      Real.exp (-bernoulliLowerTailConstant * (∑ i ∈ indices, ∫ ω, X i ω ∂μ)) := by
  classical
  let v : ℝ := ∑ i ∈ indices, ∫ ω, X i ω ∂μ
  have hint : ∀ i ∈ indices, Integrable (fun ω => Real.exp ((-1) * X i ω)) μ := by
    intro i hi
    have hid : (fun ω => Real.exp ((-1) * X i ω)) =
        (fun ω => 1 - (1 - Real.exp (-1)) * X i ω) := by
      funext ω
      rcases h01 i ω with h | h <;> simp [h]
    rw [hid]
    exact (integrable_const _).sub ((integrable_of_zero_one μ (hX i) (h01 i)).const_mul _)
  have hmgf : mgf (∑ i ∈ indices, X i) μ (-1) ≤
      Real.exp (-(1 - Real.exp (-1)) * v) := by
    rw [hind.mgf_sum hX indices]
    calc
      _ ≤ ∏ i ∈ indices,
          Real.exp (-(1 - Real.exp (-1)) * ∫ ω, X i ω ∂μ) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact mgf_nonneg
        · intro i hi
          rw [mgf_neg_one_of_zero_one μ (hX i) (h01 i)]
          have he := Real.add_one_le_exp (-(1 - Real.exp (-1)) * (∫ ω, X i ω ∂μ))
          nlinarith
      _ = Real.exp (-(1 - Real.exp (-1)) * v) := by
        rw [← Real.exp_sum]
        congr 1
        simp only [v, Finset.mul_sum]
  have hchernoff := measure_le_le_exp_mul_mgf (μ := μ)
    (X := ∑ i ∈ indices, X i) (v / 2) (show (-1 : ℝ) ≤ 0 by norm_num)
    (hind.integrable_exp_mul_sum hX hint)
  simp only [Finset.sum_apply] at hchernoff
  calc
    _ ≤ Real.exp (-(-1) * (v / 2)) * mgf (∑ i ∈ indices, X i) μ (-1) := hchernoff
    _ ≤ Real.exp (-(-1) * (v / 2)) * Real.exp (-(1 - Real.exp (-1)) * v) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-bernoulliLowerTailConstant * v) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [bernoulliLowerTailConstant]
      ring

/-- A version of the lower-tail bound with the mean replaced by the paper's
cutoff `B`. The hypotheses are exactly the numerical inequalities established
for the other-survivor count before time `s`. -/
theorem bernoulli_sum_eq_le_cutoff {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hind : iIndepFun X μ) (indices : Finset ι) {m B : ℝ}
    (hm : m ≤ (∑ i ∈ indices, ∫ ω, X i ω ∂μ) / 2)
    (hB : B / 2 ≤ ∑ i ∈ indices, ∫ ω, X i ω ∂μ) :
    μ.real {ω | (∑ i ∈ indices, X i ω) = m} ≤
      Real.exp (-(bernoulliLowerTailConstant / 2) * B) := by
  calc
    _ ≤ μ.real {ω | (∑ i ∈ indices, X i ω) ≤
        (∑ i ∈ indices, ∫ ω, X i ω ∂μ) / 2} := by
      exact measureReal_mono (by intro ω hω; exact hω.trans_le hm) (measure_ne_top _ _)
    _ ≤ Real.exp (-bernoulliLowerTailConstant * (∑ i ∈ indices, ∫ ω, X i ω ∂μ)) :=
      bernoulli_sum_lower_tail μ X hX h01 hind indices
    _ ≤ Real.exp (-(bernoulliLowerTailConstant / 2) * B) := by
      apply Real.exp_le_exp.mpr
      nlinarith [bernoulliLowerTailConstant_pos]

end

end Luce
