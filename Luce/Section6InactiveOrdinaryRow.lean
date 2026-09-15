import Luce.Section6TerminalPowerSum
import Luce.Section6InteriorTargetBound

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem rate_times_half_power_bound {d : ℝ} (hd : 0 < d) (theta : ℝ) :
    theta*(1/2 : ℝ)^(d*theta) ≤ Real.exp (-1)/(d*Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hid : (1/2 : ℝ)^(d*theta) = Real.exp (-(d*Real.log 2)*theta) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.log_div (by norm_num) (by norm_num), Real.log_one]
    congr 1
    ring
  rw [hid]
  simpa [rateKernel, survivalKernel] using rateKernel_le_exp_neg_one_div (a := theta) (mul_pos hd hl)

/-- Uniform row bound for the ordinary inactive terminal kernel, with no
upper bound on theta. The depth cutoff is more generous than required by
the proved insertion envelope. -/
theorem inactive_terminal_ordinary_row_bound {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n theta : ℝ), 0 < n → 0 < theta →
    ∀ M : ℕ, 2*(M : ℝ) ≤ n →
    (∑ k ∈ Finset.range M, (theta/((k : ℝ)+1))*
      (((k : ℝ)+1)/n)^(d*theta)) ≤ C := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1/d+2*(Real.exp (-1)/(d*Real.log 2)), by positivity, ?_⟩
  intro n theta hn ht M hMn
  by_cases hM : 0 < M
  · have hs := terminal_power_sum_half_bound hn ht.le (mul_pos hd ht) M hM hMn
    have he := rate_times_half_power_bound hd theta
    have hid : theta/(d*theta) = 1/d := by field_simp
    rw [hid] at hs
    nlinarith only [hs, he]
  · have hM0 : M = 0 := by omega
    rw [hM0]
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity

end Luce.Section6
