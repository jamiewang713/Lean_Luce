import Luce.Section4EndpointProbability
import Luce.Section4EndpointCapacityAnalytic

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace Luce

/-- Exact lower-tail exponent with a lower bound B on the true mean.
All premises are discharged by survivor means in the intended application. -/
theorem bernoulli_block_lower_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hind : iIndepFun X μ) (indices : Finset ι)
    {r B : ℝ} (hr : 0 ≤ r) (hrB : r < B)
    (hB : B ≤ ∑ i ∈ indices, ∫ ω, X i ω ∂μ) :
    μ.real {ω | (∑ i ∈ indices, X i ω) ≤ r} ≤
      Real.exp (-((B - r) ^ 2 / (2 * B))) := by
  classical
  let d : ℝ := (B - r) / B
  have hB0 : 0 < B := hr.trans_lt hrB
  have hd : 0 < d := div_pos (sub_pos.mpr hrB) hB0
  have hd1 : d ≤ 1 := (div_le_one hB0).mpr (by linarith)
  have hint : ∀ i ∈ indices, Integrable (fun ω => Real.exp ((-d) * X i ω)) μ := by
    intro i _
    have hid : (fun ω => Real.exp ((-d) * X i ω)) =
        (fun ω => 1 + (Real.exp (-d) - 1) * X i ω) := by
      funext ω
      rcases h01 i ω with h | h <;> simp [h]
    rw [hid]
    exact (integrable_const _).add ((integrable_of_zero_one μ (hX i) (h01 i)).const_mul _)
  have hmgf : mgf (∑ i ∈ indices, X i) μ (-d) ≤
      Real.exp ((Real.exp (-d) - 1) * (∑ i ∈ indices, ∫ ω, X i ω ∂μ)) := by
    rw [hind.mgf_sum hX indices]
    calc
      _ ≤ ∏ i ∈ indices, Real.exp ((Real.exp (-d) - 1) * ∫ ω, X i ω ∂μ) := by
        apply Finset.prod_le_prod (fun _ _ => mgf_nonneg)
        intro i _
        have hid : (fun ω => Real.exp ((-d) * X i ω)) =
            (fun ω => 1 + (Real.exp (-d) - 1) * X i ω) := by
          funext ω
          rcases h01 i ω with h | h <;> simp [h]
        rw [mgf, hid, integral_add (integrable_const _)
          ((integrable_of_zero_one μ (hX i) (h01 i)).const_mul _), integral_const_mul]
        simpa [add_comm] using Real.add_one_le_exp ((Real.exp (-d) - 1) * ∫ ω, X i ω ∂μ)
      _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]
  have hchernoff := measure_le_le_exp_mul_mgf (μ := μ) (X := ∑ i ∈ indices, X i)
    r (neg_nonpos.mpr hd.le) (hind.integrable_exp_mul_sum hX hint)
  simp only [Finset.sum_apply] at hchernoff
  calc
    _ ≤ Real.exp (-(-d) * r) * mgf (∑ i ∈ indices, X i) μ (-d) := hchernoff
    _ ≤ Real.exp (-(-d) * r) *
        Real.exp ((Real.exp (-d) - 1) * (∑ i ∈ indices, ∫ ω, X i ω ∂μ)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ ≤ Real.exp (d * r + (Real.exp (-d) - 1) * B) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonpos_left hB
        (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hd.le)))
      simpa using add_le_add_left this (d * r)
    _ ≤ Real.exp (d * r + (-d + d ^ 2 / 2) * B) := by
      apply Real.exp_le_exp.mpr
      have h := exp_neg_le_quadratic hd.le
      nlinarith
    _ = _ := by
      congr 1
      dsimp [d]
      field_simp
      <;> ring

end Luce
