import Luce.Section6CriticalLogSums

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem critical_reference_sum_integral {n : ℝ} {A B : ℕ}
    (hA : 1 ≤ A) (hAB : A ≤ B) (hzB : 1 ≤ Real.log n-Real.log (B : ℝ)) :
    |(∑ m ∈ Finset.Icc A B, 1/((m : ℝ)*(Real.log n-Real.log (m : ℝ))))-
      (Real.log (Real.log n-Real.log (A : ℝ))-
        Real.log (Real.log n-Real.log (B : ℝ)))| ≤ 1 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hABr : (A : ℝ) ≤ B := by exact_mod_cast hAB
  let f : ℝ → ℝ := fun x => 1/(x*(Real.log n-Real.log x))
  have hx0 {x : ℝ} (hx : x ∈ Icc (A : ℝ) B) : 0 < x := hA0.trans_le hx.1
  have hz {x : ℝ} (hx : x ∈ Icc (A : ℝ) B) : 1 ≤ Real.log n-Real.log x :=
    hzB.trans (sub_le_sub_left (Real.log_le_log (hx0 hx) hx.2) _)
  have hf (x : ℝ) : f x = (Real.log n-Real.log x)^(-(1 : ℝ))/x := by
    rw [Real.rpow_neg_one]; dsimp [f]; simp [div_eq_mul_inv,mul_comm]
  have hderiv (x : ℝ) (hx : x ∈ Icc (A : ℝ) B) :=
    critical_log_summand_deriv (p := 1) (n := n) (hx0 hx) (by linarith [hz hx])
  have hcont : ContinuousOn f (Icc (A : ℝ) B) := by
    rw [show f = (fun x => (Real.log n-Real.log x)^(-(1 : ℝ))/x) from funext hf]
    exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hanti : AntitoneOn f (Icc (A : ℝ) B) := by
    rw [show f = (fun x => (Real.log n-Real.log x)^(-(1 : ℝ))/x) from funext hf]
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hderiv x (interior_subset hx)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith [hz (interior_subset hx)]) _)
          (sub_nonpos.mpr (hz (interior_subset hx)))) (sq_nonneg _)
  have hint : (∫ x in (A : ℝ)..B, f x) =
      Real.log (Real.log n-Real.log (A : ℝ))-Real.log (Real.log n-Real.log (B : ℝ)) := by
    have hh : (∫ x in (A : ℝ)..B, f x) =
        -Real.log (Real.log n-Real.log (B : ℝ))-(-Real.log (Real.log n-Real.log (A : ℝ))) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x : ℝ => -Real.log (Real.log n-Real.log x)) _
        (hcont.intervalIntegrable_of_Icc hABr)
      intro x hx
      rw [uIcc_of_le hABr] at hx
      have h := (((Real.hasDerivAt_log (hx0 hx).ne').const_sub (Real.log n)).log
        (show Real.log n-Real.log x ≠ 0 by linarith [hz hx])).neg
      convert h using 1 <;> first | rfl | (dsimp [f]; field_simp)
    linarith
  have hup := antitone_depth_sum_le hAB hanti
  have hlo := hanti.integral_le_sum_Ico hAB
  have hlo' : (∫ x in (A : ℝ)..B, f x) ≤ ∑ m ∈ Finset.Icc A B, f m := by
    apply hlo.trans
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
      (fun m hm _ => by
        have hm' : (m : ℝ) ∈ Icc (A : ℝ) B := ⟨by exact_mod_cast (Finset.mem_Icc.mp hm).1,
          by exact_mod_cast (Finset.mem_Icc.mp hm).2⟩
        have := hz hm'
        dsimp [f]
        positivity)
  have hfirst : f A ≤ 1 := by
    dsimp [f]
    apply (div_le_one (mul_pos hA0 (by linarith [hz (left_mem_Icc.mpr hABr)]))).mpr
    exact one_le_mul_of_one_le_of_one_le hAr (hz (left_mem_Icc.mpr hABr))
  rw [hint] at hup hlo'
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end Luce.Section6
