import Luce.Section6CriticalLogSums

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem critical_log_error_power_bound {z : ℝ} (hz : 1 ≤ z) :
    (1+Real.log z)/z^2 ≤ 3*z^(-(3/2 : ℝ)) := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hp : 1 ≤ z^(1/2 : ℝ) := Real.one_le_rpow hz (by norm_num)
  have hl := Real.log_le_rpow_div hz0.le (show (0 : ℝ) < 1/2 by norm_num)
  have heq : z^(1/2 : ℝ)/z^2 = z^(-(3/2 : ℝ)) := by
    rw [← Real.rpow_natCast z 2,← Real.rpow_sub hz0]
    congr 1
    norm_num
  calc
    _ ≤ (3*z^(1/2 : ℝ))/z^2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg z)
    _ = _ := by rw [mul_div_assoc,heq]

/-- Uniform summability of the logarithmic error in the critical hazard. -/
theorem critical_log_error_sum {n : ℝ} {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (hzB : (3/2 : ℝ) ≤ Real.log n-Real.log (B : ℝ)) :
    (∑ m ∈ Finset.Icc A B,
      (1+Real.log (Real.log n-Real.log (m : ℝ)))/
        ((m : ℝ)*(Real.log n-Real.log (m : ℝ))^2)) ≤ 9 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hsum := critical_log_root_sum (n := n) (p := 3/2) (by norm_num) hA hAB hzB
  have hs : (∑ m ∈ Finset.Icc A B,
      (1+Real.log (Real.log n-Real.log (m : ℝ)))/
        ((m : ℝ)*(Real.log n-Real.log (m : ℝ))^2)) ≤
      3*(∑ m ∈ Finset.Icc A B, (Real.log n-Real.log (m : ℝ))^(-(3/2 : ℝ))/(m : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hm0 : (0 : ℝ) < m := hA0.trans_le (by exact_mod_cast (Finset.mem_Icc.mp hm).1)
    have hmB : (m : ℝ) ≤ B := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hz : 1 ≤ Real.log n-Real.log (m : ℝ) := by
      have := Real.log_le_log hm0 hmB
      linarith
    calc
      _ = ((1+Real.log (Real.log n-Real.log (m : ℝ)))/(Real.log n-Real.log (m : ℝ))^2)/m := by
        rw [div_div]; congr 1; ring
      _ ≤ (3*(Real.log n-Real.log (m : ℝ))^(-(3/2 : ℝ)))/m :=
        div_le_div_of_nonneg_right (critical_log_error_power_bound hz) hm0.le
      _ = _ := by ring
  norm_num at hsum
  linarith

theorem critical_inverse_square_sum {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ m ∈ Finset.Icc A B, 1/(m : ℝ)^2) ≤ 2 := by
  have hB := hA.trans hAB
  have h := left_excursion_depth_sum (kappa := 1) zero_lt_one (A := 1) (B := B) (by omega) hB
  norm_num only [Nat.cast_one,Real.one_rpow,one_mul,one_div_one] at h
  have hEq (m : ℕ) : (m : ℝ)^(-(2 : ℝ)) = 1/(m : ℝ)^2 := by
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num,Real.rpow_natCast]
    simp only [one_div]
  simp_rw [hEq] at h
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc hA le_rfl)
    (fun m _ _ => by positivity)).trans h

/-- The complete scalar error envelope sums uniformly over every
interval in a fixed critical corner. -/
theorem critical_main_error_sum {eta n : ℝ} (heta : 0 < eta) (hn : 0 < n)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBn : (B : ℝ) ≤ n)
    (hzB : (3/2 : ℝ) ≤ Real.log n-Real.log (B : ℝ)) :
    (∑ m ∈ Finset.Icc A B, (1/((m : ℝ)*(Real.log n-Real.log (m : ℝ))))*
      ((1+Real.log (Real.log n-Real.log (m : ℝ)))/(Real.log n-Real.log (m : ℝ))+
        1/(m : ℝ)+((m : ℝ)/n)^eta)) ≤ 12+1/eta := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hB0 : (0 : ℝ) < B := hA0.trans_le (by exact_mod_cast hAB)
  have hlog := critical_log_error_sum hA hAB hzB
  have hinv := critical_inverse_square_sum hA hAB
  have hpower := right_excursion_kernel_sum heta hA hAB
  have hz (m : ℕ) (hm : m ∈ Finset.Icc A B) : 1 ≤ Real.log n-Real.log (m : ℝ) := by
    have hm0 : (0 : ℝ) < m := hA0.trans_le (by exact_mod_cast (Finset.mem_Icc.mp hm).1)
    have hmB : (m : ℝ) ≤ B := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have := Real.log_le_log hm0 hmB
    linarith
  have hsum : (∑ m ∈ Finset.Icc A B, (1/((m : ℝ)*(Real.log n-Real.log (m : ℝ))))*
      ((1+Real.log (Real.log n-Real.log (m : ℝ)))/(Real.log n-Real.log (m : ℝ))+
        1/(m : ℝ)+((m : ℝ)/n)^eta)) ≤
      (∑ m ∈ Finset.Icc A B, (1+Real.log (Real.log n-Real.log (m : ℝ)))/
        ((m : ℝ)*(Real.log n-Real.log (m : ℝ))^2))+
      (∑ m ∈ Finset.Icc A B, 1/(m : ℝ)^2)+
      ∑ m ∈ Finset.Icc A B, (1/(m : ℝ))*((m : ℝ)/B)^eta := by
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m hm
    have hm0 : (0 : ℝ) < m := hA0.trans_le (by exact_mod_cast (Finset.mem_Icc.mp hm).1)
    have hz0 : 0 < Real.log n-Real.log (m : ℝ) := lt_of_lt_of_le zero_lt_one (hz m hm)
    have hzInv : 1/(Real.log n-Real.log (m : ℝ)) ≤ 1 := (div_le_one hz0).mpr (hz m hm)
    have hpow : ((m : ℝ)/n)^eta ≤ ((m : ℝ)/B)^eta :=
      Real.rpow_le_rpow (div_nonneg hm0.le hn.le)
        (div_le_div_of_nonneg_left hm0.le hB0 hBn) heta.le
    have h1 := mul_le_mul_of_nonneg_left hzInv (show 0 ≤ 1/(m : ℝ)^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left
      ((mul_le_of_le_one_left (Real.rpow_nonneg (div_nonneg hm0.le hn.le) _) hzInv).trans hpow)
      (show 0 ≤ 1/(m : ℝ) by positivity)
    calc
      _ = (1+Real.log (Real.log n-Real.log (m : ℝ)))/
          ((m : ℝ)*(Real.log n-Real.log (m : ℝ))^2)+
          (1/(m : ℝ)^2)*(1/(Real.log n-Real.log (m : ℝ)))+
          (1/(m : ℝ))*((1/(Real.log n-Real.log (m : ℝ)))*((m : ℝ)/n)^eta) := by
        field_simp
      _ ≤ _ := by simpa only [mul_one] using add_le_add (add_le_add le_rfl h1) h2
  linarith

end Luce.Section6
