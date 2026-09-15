import Luce.Section6TerminalPowerSum
import Luce.Section6ActiveOrdinaryRows

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Exact removal of the outside-source weight, without changing the kernel. -/
theorem outside_left_weighted_power_identity {n h : ℝ} (hn : 0 < n) (hh : 0 < h)
    (theta alpha kappa : ℝ) :
    (n/h)^kappa*(theta*(h/n)^alpha/h) = (theta/h)*(h/n)^(alpha-kappa) := by
  rw [reverse_ratio_power hn hh kappa]
  have he : (h/n)^(-kappa)*(h/n)^alpha = (h/n)^(alpha-kappa) := by
    rw [← Real.rpow_add (div_pos hh hn)]
    congr 1
    ring
  calc
    _ = (theta/h)*((h/n)^(-kappa)*(h/n)^alpha) := by ring
    _ = _ := by rw [he]

/-- The ordinary left-target contribution with the larger weight (n/h)^kappa.
The rate factor is retained; concrete outside sources have a profile-derived
upper rate bound. The only power restriction is kappa<alpha. -/
theorem outside_left_weighted_sum_bound {n theta alpha kappa d : ℝ}
    (hn : 0 < n) (htheta : 0 ≤ theta) (hk : kappa < alpha) (hd : 0 ≤ d)
    (M : ℕ) (hMn : 2*(M : ℝ) ≤ n) :
    (∑ k ∈ Finset.range M,
      (n/((k : ℝ)+1))^kappa*(theta*(((k : ℝ)+1)/n)^alpha/((k : ℝ)+1))*
        Real.exp (-d*(theta*(((k : ℝ)+1)/n)^alpha))) ≤
      theta*(1/(alpha-kappa)+2*(1/2 : ℝ)^(alpha-kappa)) := by
  have ht : 0 < alpha-kappa := sub_pos.mpr hk
  by_cases hM : M = 0
  · subst M
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  have hsum := terminal_power_sum_half_bound hn htheta ht M (Nat.pos_of_ne_zero hM) hMn
  have hle : (∑ k ∈ Finset.range M,
      (n/((k : ℝ)+1))^kappa*(theta*(((k : ℝ)+1)/n)^alpha/((k : ℝ)+1))*
        Real.exp (-d*(theta*(((k : ℝ)+1)/n)^alpha))) ≤
      ∑ k ∈ Finset.range M, (theta/((k : ℝ)+1))*(((k : ℝ)+1)/n)^(alpha-kappa) := by
    apply Finset.sum_le_sum
    intro k _
    have hh : 0 < (k : ℝ)+1 := by positivity
    have he : Real.exp (-d*(theta*(((k : ℝ)+1)/n)^alpha)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd) (by positivity))
    rw [outside_left_weighted_power_identity hn hh]
    exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)
  exact (hle.trans hsum).trans_eq (by ring)

end Luce.Section6
