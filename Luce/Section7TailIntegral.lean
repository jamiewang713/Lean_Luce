import Luce.Section7Definitions

/-! # Splitting density-weighted probabilities at a real cutoff -/

open scoped BigOperators
open MeasureTheory Set

namespace Luce.Section7
noncomputable section

/-- The analytic part of the distribution-free tail estimate. -/
theorem density_integral_bound {ι : Type*} (indices : Finset ι)
    (g : ι → ClockDensity) (p : ι → ℝ → ℝ) (s q : ℝ) (h : ℝ → ℝ)
    (hq : 0 ≤ q) (hh : IntegrableOn h (Ioi s))
    (hpmeas : ∀ i ∈ indices, Measurable (p i))
    (hp : ∀ i ∈ indices, ∀ t, 0 ≤ p i t ∧ p i t ≤ 1)
    (hearly : ∀ i ∈ indices, ∀ t ≤ s, p i t ≤ q)
    (hhnonneg : ∀ t ∈ Ioi s, 0 ≤ h t)
    (henv : ∀ i ∈ indices, ∀ t ∈ Ioi s, (g i).density t ≤ h t)
    (hlate : ∀ t ∈ Ioi s, ∑ i ∈ indices, p i t ≤ 2) :
    (∑ i ∈ indices, ∫ t, (g i).density t * p i t) ≤
      (indices.card : ℝ) * q + 2 * ∫ t in Ioi s, h t := by
  let f : ℝ → ℝ := fun t => ∑ i ∈ indices, (g i).density t * p i t
  have hint : ∀ i ∈ indices, Integrable (fun t => (g i).density t * p i t) := by
    intro i hi
    apply (g i).integrable.mono' ((g i).measurable.mul (hpmeas i hi)).aestronglyMeasurable
    filter_upwards [] with t
    change ‖(g i).density t * p i t‖ ≤ (g i).density t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ((g i).nonneg t) (hp i hi t).1)]
    exact mul_le_of_le_one_right ((g i).nonneg t) (hp i hi t).2
  have hf : Integrable f := integrable_finsetSum _ hint
  have hearlyBound : (∫ t in Iic s, f t) ≤ (indices.card : ℝ) * q := by
    rw [show (∫ t in Iic s, f t) =
      ∑ i ∈ indices, ∫ t in Iic s, (g i).density t * p i t from
        integral_finsetSum _ (fun i hi => (hint i hi).integrableOn)]
    calc
      _ ≤ ∑ i ∈ indices, q := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          _ ≤ ∫ t in Iic s, (g i).density t * q := by
            apply integral_mono_ae (hint i hi).integrableOn ((g i).integrable.mul_const q).integrableOn
            filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
            exact mul_le_mul_of_nonneg_left (hearly i hi t ht) ((g i).nonneg t)
          _ ≤ ∫ t, (g i).density t * q := by
            exact setIntegral_le_integral ((g i).integrable.mul_const q)
              (Filter.Eventually.of_forall fun t => mul_nonneg ((g i).nonneg t) hq)
          _ = q := by rw [integral_mul_const, (g i).integral_one, one_mul]
      _ = _ := by simp [nsmul_eq_mul]
  have hlateBound : (∫ t in Ioi s, f t) ≤ 2 * ∫ t in Ioi s, h t := by
    rw [← integral_const_mul]
    apply integral_mono_ae hf.integrableOn (hh.const_mul 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      _ ≤ ∑ i ∈ indices, h t * p i t := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_right (henv i hi t ht) (hp i hi t).1
      _ = h t * ∑ i ∈ indices, p i t := (Finset.mul_sum _ _ _).symm
      _ ≤ h t * 2 := mul_le_mul_of_nonneg_left (hlate t ht) (hhnonneg t ht)
      _ = 2 * h t := mul_comm _ _
  rw [← integral_finsetSum _ hint]
  change (∫ t, f t) ≤ _
  rw [← integral_add_compl measurableSet_Iic hf, compl_Iic]
  exact add_le_add hearlyBound hlateBound

end
end Luce.Section7
