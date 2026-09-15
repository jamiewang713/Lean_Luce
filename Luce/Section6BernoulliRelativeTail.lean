import Luce.Section6BernoulliUpperTail

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

theorem bernoulli_sum_exp_integrable {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hind : iIndepFun X μ) (indices : Finset ι) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * (∑ i ∈ indices, X i) ω)) μ := by
  apply hind.integrable_exp_mul_sum hX
  intro i _
  have he : (fun ω => Real.exp (t * X i ω)) =
      (fun ω => 1 + (Real.exp t - 1) * X i ω) := by
    funext ω
    rcases h01 i ω with h | h <;> simp [h]
  rw [he]
  exact (integrable_const _).add ((integrable_of_zero_one μ (hX i) (h01 i)).const_mul _)

/-- Relative upper tail at arbitrary shrinking relative scale. The
variance scale is the sum of the Bernoulli means, not the number of labels. -/
theorem bernoulli_relative_upper_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hind : iIndepFun X μ) (indices : Finset ι) {eps : ℝ}
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) :
    let m := ∑ i ∈ indices, ∫ ω, X i ω ∂μ
    μ.real {ω | (1+eps)*m ≤ ∑ i ∈ indices, X i ω} ≤ Real.exp (-eps^2*m/4) := by
  let m := ∑ i ∈ indices, ∫ ω, X i ω ∂μ
  have hm : 0 ≤ m := Finset.sum_nonneg fun i _ => integral_nonneg fun ω => by
    rcases h01 i ω with h | h <;> simp [h]
  have ht : |eps/2| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hr := (le_abs_self (Real.exp (eps/2)-1-eps/2)).trans
    (Real.abs_exp_sub_one_sub_id_le ht)
  have hc := measure_ge_le_exp_mul_mgf (μ := μ) (X := ∑ i ∈ indices, X i)
    ((1+eps)*m) (show 0 ≤ eps/2 by positivity)
    (bernoulli_sum_exp_integrable μ X hX h01 hind indices (eps/2))
  simp only [Finset.sum_apply] at hc
  have hb := bernoulli_mgf_upper μ X hX h01 hind indices (eps/2)
  calc
    _ ≤ Real.exp (-(eps/2)*((1+eps)*m))*mgf (∑ i ∈ indices, X i) μ (eps/2) := hc
    _ ≤ Real.exp (-(eps/2)*((1+eps)*m))*Real.exp ((Real.exp (eps/2)-1)*m) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ ≤ Real.exp (-eps^2*m/4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_right hr hm]

/-- Matching relative lower tail, including zero mean and zero deviation. -/
theorem bernoulli_relative_lower_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hind : iIndepFun X μ) (indices : Finset ι) {eps : ℝ}
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) :
    let m := ∑ i ∈ indices, ∫ ω, X i ω ∂μ
    μ.real {ω | (∑ i ∈ indices, X i ω) ≤ (1-eps)*m} ≤ Real.exp (-eps^2*m/4) := by
  let m := ∑ i ∈ indices, ∫ ω, X i ω ∂μ
  have hm : 0 ≤ m := Finset.sum_nonneg fun i _ => integral_nonneg fun ω => by
    rcases h01 i ω with h | h <;> simp [h]
  have ht : |-(eps/2)| ≤ 1 := by rw [abs_neg, abs_of_nonneg (by positivity)]; linarith
  have hr := (le_abs_self (Real.exp (-(eps/2))-1-(-(eps/2)))).trans
    (Real.abs_exp_sub_one_sub_id_le ht)
  have hc := measure_le_le_exp_mul_mgf (μ := μ) (X := ∑ i ∈ indices, X i)
    ((1-eps)*m) (neg_nonpos.mpr (div_nonneg heps (by norm_num : (0 : ℝ) ≤ 2)))
    (bernoulli_sum_exp_integrable μ X hX h01 hind indices (-(eps/2)))
  simp only [Finset.sum_apply] at hc
  have hb := bernoulli_mgf_upper μ X hX h01 hind indices (-(eps/2))
  calc
    _ ≤ Real.exp (-(-(eps/2))*((1-eps)*m))*mgf (∑ i ∈ indices, X i) μ (-(eps/2)) := hc
    _ ≤ Real.exp (-(-(eps/2))*((1-eps)*m))*Real.exp ((Real.exp (-(eps/2))-1)*m) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ ≤ Real.exp (-eps^2*m/4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_right hr hm]

end Luce.Section6
