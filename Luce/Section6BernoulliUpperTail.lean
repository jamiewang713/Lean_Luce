import Luce.EndpointProbability

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

theorem log_two_sub_half_pos : 0 < Real.log 2 - 1/2 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≠ 1)
  rw [Real.log_inv] at h
  norm_num at h
  linarith

/-- Bernoulli MGF bound for arbitrary real tilt and nonidentical probabilities. -/
theorem bernoulli_mgf_upper {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hind : iIndepFun X μ) (indices : Finset ι) (s : ℝ) :
    mgf (∑ i ∈ indices, X i) μ s ≤
      Real.exp ((Real.exp s-1)*(∑ i ∈ indices, ∫ ω, X i ω ∂μ)) := by
  rw [hind.mgf_sum hX indices]
  calc
    _ ≤ ∏ i ∈ indices, Real.exp ((Real.exp s-1)*∫ ω, X i ω ∂μ) := by
      apply Finset.prod_le_prod (fun _ _ => mgf_nonneg)
      intro i _
      have he : (fun ω => Real.exp (s*X i ω)) = (fun ω => 1+(Real.exp s-1)*X i ω) := by
        funext ω
        rcases h01 i ω with h | h <;> simp [h]
      rw [mgf, he, integral_add (integrable_const _)
        ((integrable_of_zero_one μ (hX i) (h01 i)).const_mul _), integral_const_mul]
      simpa [add_comm] using Real.add_one_le_exp ((Real.exp s-1)*∫ ω, X i ω ∂μ)
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

/-- If the mean is at most half the threshold, the upper tail decays
exponentially in that threshold. No identical-distribution input is needed. -/
theorem bernoulli_upper_tail_of_mean_le_half {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hind : iIndepFun X μ) (indices : Finset ι) {R : ℝ}
    (hmean : (∑ i ∈ indices, ∫ ω, X i ω ∂μ) ≤ R/2) :
    μ.real {ω | R ≤ ∑ i ∈ indices, X i ω} ≤ Real.exp (-((Real.log 2-1/2)*R)) := by
  have hint : ∀ i ∈ indices, Integrable (fun ω => Real.exp (Real.log 2*X i ω)) μ := by
    intro i _
    have he : (fun ω => Real.exp (Real.log 2*X i ω)) = (fun ω => 1+X i ω) := by
      funext ω
      rcases h01 i ω with h | h <;> norm_num [h, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [he]
    exact (integrable_const _).add (integrable_of_zero_one μ (hX i) (h01 i))
  have hc := measure_ge_le_exp_mul_mgf (μ := μ) (X := ∑ i ∈ indices, X i) R
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (hind.integrable_exp_mul_sum hX hint)
  simp only [Finset.sum_apply] at hc
  have hm := bernoulli_mgf_upper μ X hX h01 hind indices (Real.log 2)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hm
  calc
    _ ≤ Real.exp (-(Real.log 2)*R)*mgf (∑ i ∈ indices, X i) μ (Real.log 2) := hc
    _ ≤ Real.exp (-(Real.log 2)*R)*
        Real.exp ((2-1)*(∑ i ∈ indices, ∫ ω, X i ω ∂μ)) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ ≤ Real.exp (-((Real.log 2-1/2)*R)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith

end Luce.Section6
