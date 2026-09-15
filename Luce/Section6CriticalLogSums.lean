import Luce.Section6ExcursionDepthSums
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem critical_log_primitive_deriv {p n x : ℝ} (hp : p ≠ 1)
    (hx : 0 < x) (hz : 0 < Real.log n-Real.log x) :
    HasDerivAt (fun y : ℝ => (Real.log n-Real.log y)^(1-p)/(p-1))
      ((Real.log n-Real.log x)^(-p)/x) x := by
  have h := (((Real.hasDerivAt_log hx.ne').const_sub (Real.log n)).rpow_const
    (p := 1-p) (Or.inl hz.ne')).div_const (p-1)
  convert h using 1 <;> first | rfl | (rw [show 1-p-1 = -p by ring]; field_simp [sub_ne_zero.mpr hp] <;> ring)

theorem critical_log_summand_deriv {p n x : ℝ}
    (hx : 0 < x) (hz : 0 < Real.log n-Real.log x) :
    HasDerivAt (fun y : ℝ => (Real.log n-Real.log y)^(-p)/y)
      (((Real.log n-Real.log x)^(-p-1))*(p-(Real.log n-Real.log x))/x^2) x := by
  have h := (((Real.hasDerivAt_log hx.ne').const_sub (Real.log n)).rpow_const
    (p := -p) (Or.inl hz.ne')).div (hasDerivAt_id x) hx.ne'
  have heq : (Real.log n-Real.log x)^(-p) =
        (Real.log n-Real.log x)^(-p-1)*(Real.log n-Real.log x) := by
      calc
        _ = (Real.log n-Real.log x)^((-p-1)+1) := by ring_nf
        _ = _ := by rw [Real.rpow_add hz,Real.rpow_one]
  convert h using 1 <;> first | rfl | (simp only [id_eq]; rw [heq]; field_simp <;> ring)

/-- Uniform summability of the coarser critical rooted-cycle bound.
The lower logarithmic cutoff may be chosen once for each fixed p > 1. -/
theorem critical_log_root_sum {p n : ℝ} (hp : 1 < p) {A B : ℕ}
    (hA : 1 ≤ A) (hAB : A ≤ B) (hzB : p ≤ Real.log n-Real.log (B : ℝ)) :
    (∑ m ∈ Finset.Icc A B, (Real.log n-Real.log (m : ℝ))^(-p)/(m : ℝ)) ≤
      1+1/(p-1) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hABr : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hB0 : (0 : ℝ) < B := hA0.trans_le hABr
  let f : ℝ → ℝ := fun x => (Real.log n-Real.log x)^(-p)/x
  have hx0 {x : ℝ} (hx : x ∈ Icc (A : ℝ) B) : 0 < x := hA0.trans_le hx.1
  have hz {x : ℝ} (hx : x ∈ Icc (A : ℝ) B) : p ≤ Real.log n-Real.log x :=
    hzB.trans (sub_le_sub_left (Real.log_le_log (hx0 hx) hx.2) _)
  have hderiv (x : ℝ) (hx : x ∈ Icc (A : ℝ) B) :=
    critical_log_summand_deriv (p := p) (n := n) (hx0 hx) (by linarith [hz hx])
  have hcont : ContinuousOn f (Icc (A : ℝ) B) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hanti : AntitoneOn f (Icc (A : ℝ) B) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hderiv x (interior_subset hx)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith [hz (interior_subset hx)]) _)
          (sub_nonpos.mpr (hz (interior_subset hx)))) (sq_nonneg _)
  have hint : IntervalIntegrable f volume (A : ℝ) B := hcont.intervalIntegrable_of_Icc hABr
  have heq : (∫ x in (A : ℝ)..B, f x) =
      (Real.log n-Real.log (B : ℝ))^(1-p)/(p-1)-
        (Real.log n-Real.log (A : ℝ))^(1-p)/(p-1) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => (Real.log n-Real.log y)^(1-p)/(p-1)) _ hint
    intro x hx
    rw [uIcc_of_le hABr] at hx
    exact critical_log_primitive_deriv (ne_of_gt hp) (hx0 hx) (by linarith [hz hx])
  have hsum := antitone_depth_sum_le hAB hanti
  rw [heq] at hsum
  have hpA : (Real.log n-Real.log (A : ℝ))^(-p) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hz (left_mem_Icc.mpr hABr)]) (by linarith)
  have hpB : (Real.log n-Real.log (B : ℝ))^(1-p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hfA : f A ≤ 1 := by
    apply (div_le_div_of_nonneg_right hpA hA0.le).trans
    exact (div_le_one hA0).mpr hAr
  have hlast : 0 ≤ (Real.log n-Real.log (A : ℝ))^(1-p)/(p-1) :=
    div_nonneg (Real.rpow_nonneg (by linarith [hz (left_mem_Icc.mpr hABr)]) _) (sub_pos.mpr hp).le
  have hfirst := div_le_div_of_nonneg_right hpB (sub_pos.mpr hp).le
  change (∑ m ∈ Finset.Icc A B, f m) ≤ _
  linarith only [hsum,hfA,hlast,hfirst]

end Luce.Section6
