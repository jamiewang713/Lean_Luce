import Luce.Section6PositivePowerSumUpper

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem terminal_power_kernel_factor {a n : ℝ} (ha : 0 < a) (hn : 0 < n) (theta t : ℝ) :
    (theta/a)*(a/n)^t = (theta/n^t)*a^(t-1) := by
  rw [Real.div_rpow ha.le hn.le, Real.rpow_sub ha, Real.rpow_one]
  ring

/-- Exact integral-comparison upper bound before bounding the two endpoint
corrections uniformly in the source rate. -/
theorem terminal_power_sum_upper {n theta t : ℝ} (hn : 0 < n)
    (htheta : 0 ≤ theta) (ht : 0 < t) (M : ℕ) (hM : 0 < M) :
    (∑ k ∈ Finset.range M, (theta/((k : ℝ)+1))*(((k : ℝ)+1)/n)^t) ≤
      (theta/t)*((M : ℝ)/n)^t+theta/n^t+
        (theta/(M : ℝ))*((M : ℝ)/n)^t := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hs := positive_power_sum_upper (z := t-1) (by linarith) M hM
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ theta/n^t by positivity)
  have he : (∑ k ∈ Finset.range M, (theta/((k : ℝ)+1))*(((k : ℝ)+1)/n)^t) =
      (theta/n^t)*(∑ k ∈ Finset.range M, ((k : ℝ)+1)^(t-1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact terminal_power_kernel_factor (by positivity) hn theta t
  rw [he]
  have hid : (theta/n^t)*((M : ℝ)^((t-1)+1)/((t-1)+1)+1+(M : ℝ)^(t-1)) =
      (theta/t)*((M : ℝ)/n)^t+theta/n^t+
        (theta/(M : ℝ))*((M : ℝ)/n)^t := by
    rw [sub_add_cancel, Real.div_rpow hMR.le hn.le, Real.rpow_sub hMR, Real.rpow_one]
    ring
  exact hid ▸ hs'

/-- Restricting targets to the first half of the depth range bounds the
integral term and both discretization corrections. -/
theorem terminal_power_sum_half_bound {n theta t : ℝ} (hn : 0 < n)
    (htheta : 0 ≤ theta) (ht : 0 < t) (M : ℕ) (hM : 0 < M)
    (hMn : 2*(M : ℝ) ≤ n) :
    (∑ k ∈ Finset.range M, (theta/((k : ℝ)+1))*(((k : ℝ)+1)/n)^t) ≤
      theta/t+2*theta*(1/2 : ℝ)^t := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hn2 : (2 : ℝ) ≤ n := by linarith
  have hu : (M : ℝ)/n ≤ 1/2 := (div_le_iff₀ hn).mpr (by linarith)
  have hup : ((M : ℝ)/n)^t ≤ (1/2 : ℝ)^t := Real.rpow_le_rpow (by positivity) hu ht.le
  have hup1 : ((M : ℝ)/n)^t ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) ht.le
  have h1 := mul_le_mul_of_nonneg_left hup1 (show 0 ≤ theta/t by positivity)
  have hinv : 1/n ≤ (1/2 : ℝ) := (div_le_div_iff₀ hn (by norm_num)).mpr (by linarith)
  have hip := Real.rpow_le_rpow (show 0 ≤ 1/n by positivity) hinv ht.le
  have hid : theta/n^t = theta*(1/n)^t := by rw [Real.div_rpow zero_le_one hn.le, Real.one_rpow]; ring
  have h2 : theta/n^t ≤ theta*(1/2 : ℝ)^t := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left hip htheta
  have h3 : (theta/(M : ℝ))*((M : ℝ)/n)^t ≤ theta*(1/2 : ℝ)^t :=
    mul_le_mul (div_le_self htheta hM1) hup (by positivity) htheta
  have hs := terminal_power_sum_upper hn htheta ht M hM
  nlinarith only [hs, h1, h2, h3]

end Luce.Section6
