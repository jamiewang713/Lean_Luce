import Luce.Section6OneGapMoment
import Luce.Section6KernelPerturbation

noncomputable section
namespace Luce.Section6

/-- Taylor expansion of an actual normalized gap, retaining all of the
survival decay. The spacing is arbitrary and need not be truncated. -/
theorem normalized_gap_taylor_with_decay {a W t xi : ℝ}
    (ha : 0 ≤ a) (hW : 0 < W) (hxi : 0 ≤ xi) :
    |exponentialGapMass a t (xi/W) -
      ((a/W)*survivalKernel t a)*xi| ≤
      ((a/W)^2*survivalKernel t a)*xi^2 := by
  have htay := exponentialGapMass_taylor ha (le_rfl : (0 : ℝ) ≤ 0)
    (div_nonneg hxi hW.le)
  have hid : exponentialGapMass a t (xi/W) - ((a/W)*survivalKernel t a)*xi =
      survivalKernel t a * (exponentialGapMass a 0 (xi/W)-a*(xi/W)) := by
    rw [exponentialGapMass_factor, exponentialGapMass_factor]
    simp only [survivalKernel, neg_zero, zero_mul, Real.exp_zero, one_mul]
    ring
  simp only [rateKernel, survivalKernel, neg_zero, zero_mul, Real.exp_zero, mul_one] at htay
  rw [hid, abs_mul, abs_of_pos (survivalKernel_pos t a)]
  calc
    _ ≤ survivalKernel t a*(a^2*(xi/W)^2) :=
      mul_le_mul_of_nonneg_left htay (survivalKernel_pos t a).le
    _ = _ := by ring

/-- Comparison with a deterministic coefficient. All random quantities
remain pointwise variables; this statement asserts no independence. -/
theorem normalized_gap_comparison {a W t xi K B E R : ℝ}
    (ha : 0 ≤ a) (hW : 0 < W) (hxi : 0 ≤ xi) (hK : 0 ≤ K)
    (hcoef : (a/W)*survivalKernel t a ≤ B) (hKB : K ≤ B)
    (herr : |(a/W)*survivalKernel t a-K| ≤ E)
    (hrem : (a/W)^2*survivalKernel t a ≤ R) :
    0 ≤ exponentialGapMass a t (xi/W) ∧
    exponentialGapMass a t (xi/W) ≤ B*xi ∧
    0 ≤ K*xi ∧ K*xi ≤ B*xi ∧
    |exponentialGapMass a t (xi/W)-K*xi| ≤ E*xi+R*xi^2 := by
  have hnon := exponentialGapMass_nonneg (s := t) ha (div_nonneg hxi hW.le)
  have hbound : exponentialGapMass a t (xi/W) ≤ B*xi := by
    calc
      _ ≤ a*(xi/W)*survivalKernel t a :=
        exponentialGapMass_le_survival ha (div_nonneg hxi hW.le)
      _ = ((a/W)*survivalKernel t a)*xi := by ring
      _ ≤ B*xi := mul_le_mul_of_nonneg_right hcoef hxi
  refine ⟨hnon, hbound, mul_nonneg hK hxi,
    mul_le_mul_of_nonneg_right hKB hxi, ?_⟩
  calc
    _ ≤ |exponentialGapMass a t (xi/W)-((a/W)*survivalKernel t a)*xi| +
        |((a/W)*survivalKernel t a)*xi-K*xi| := abs_sub_le _ _ _
    _ = |exponentialGapMass a t (xi/W)-((a/W)*survivalKernel t a)*xi| +
        |(a/W)*survivalKernel t a-K| * xi := by rw [← sub_mul, abs_mul, abs_of_nonneg hxi]
    _ ≤ ((a/W)^2*survivalKernel t a)*xi^2+E*xi :=
      add_le_add (normalized_gap_taylor_with_decay ha hW hxi)
        (mul_le_mul_of_nonneg_right herr hxi)
    _ ≤ R*xi^2+E*xi := add_le_add
      (mul_le_mul_of_nonneg_right hrem (sq_nonneg xi)) le_rfl
    _ = _ := by ring

/-- Telescope the normalized-gap errors without dividing by a spacing.
The statement also covers an empty family and vanishing spacings. -/
theorem normalized_gap_product_comparison {ι : Type*} [Fintype ι]
    (X K B eps invDepth xi : ι → ℝ)
    (hX : ∀ i, 0 ≤ X i) (hK : ∀ i, 0 ≤ K i)
    (hB : ∀ i, 0 ≤ B i) (heps : ∀ i, 0 ≤ eps i)
    (hi : ∀ i, 0 ≤ invDepth i) (hxi : ∀ i, 0 ≤ xi i)
    (hXB : ∀ i, X i ≤ B i*xi i) (hKB : ∀ i, K i ≤ B i)
    (herr : ∀ i, |X i-K i*xi i| ≤ B i*(eps i*xi i+invDepth i*xi i^2)) :
    |(∏ i, X i)-(∏ i, K i)*(∏ i : ι, xi i)| ≤
      (∏ i, B i)*((∑ i : ι, (eps i+invDepth i*xi i))*(∏ i : ι, xi i)) := by
  have hp := abs_prod_sub_prod_le_relative Finset.univ X (fun i => K i*xi i)
    (fun i => B i*xi i) (fun i => eps i+invDepth i*xi i)
    (fun i _ => by rw [abs_of_nonneg (hX i)]; exact hXB i)
    (fun i _ => by
      rw [abs_of_nonneg (mul_nonneg (hK i) (hxi i))]
      exact mul_le_mul_of_nonneg_right (hKB i) (hxi i))
    (fun i _ => mul_nonneg (hB i) (hxi i))
    (fun i _ => add_nonneg (heps i) (mul_nonneg (hi i) (hxi i)))
    (fun i _ => (herr i).trans_eq (by ring))
  simpa only [Finset.prod_mul_distrib, mul_left_comm, mul_assoc] using hp

end Luce.Section6
