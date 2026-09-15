import Luce.Section6CriticalReferenceSum

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem critical_reference_mass_bound {n eps : ℝ} (hn : 0 < n) (heps : 0 < eps)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hln : 1 ≤ Real.log n)
    (hlogA : Real.log (A : ℝ) ≤ (3/4 : ℝ)*Real.log n)
    (hzB : 1 ≤ Real.log n-Real.log (B : ℝ)) (hB : eps*n/2 ≤ (B : ℝ)) :
    |(∑ m ∈ Finset.Icc A B, 1/((m : ℝ)*(Real.log n-Real.log (m : ℝ))))-
      Real.log (Real.log n)| ≤ 1+Real.log 4+2/eps := by
  have hAp : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hBp : (0 : ℝ) < B := hAp.trans_le (by exact_mod_cast hAB)
  have hlogA0 : 0 ≤ Real.log (A : ℝ) := Real.log_natCast_nonneg _
  have hL : 0 < Real.log n := by linarith
  have hzA : 0 < Real.log n-Real.log (A : ℝ) := by linarith
  have hAu := Real.log_le_log hzA (show Real.log n-Real.log (A : ℝ) ≤ Real.log n by linarith)
  have hAl := Real.log_le_log (show 0 < Real.log n/4 by positivity)
    (show Real.log n/4 ≤ Real.log n-Real.log (A : ℝ) by linarith)
  rw [Real.log_div hL.ne' (by norm_num)] at hAl
  have hratio : n/(B : ℝ) ≤ 2/eps := by
    apply (div_le_div_iff₀ hBp heps).mpr
    nlinarith
  have hBu : Real.log n-Real.log (B : ℝ) ≤ 2/eps := by
    rw [← Real.log_div hn.ne' hBp.ne']
    exact (Real.log_le_sub_one_of_pos (div_pos hn hBp)).trans (by linarith)
  have hBB : 0 ≤ Real.log (Real.log n-Real.log (B : ℝ)) := Real.log_nonneg hzB
  have hBBu : Real.log (Real.log n-Real.log (B : ℝ)) ≤ 2/eps :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hh := critical_reference_sum_integral hA hAB hzB
  rw [abs_le] at hh ⊢
  constructor <;> linarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]

end Luce.Section6
