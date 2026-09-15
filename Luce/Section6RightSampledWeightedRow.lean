import Luce.Section6WeightedKernelComparison
import Luce.Section6SampledRateUpper
import Luce.Section6RateTimeLower

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- The ordinary same-corner right weighted row for the actual sampled rates.
The lower comparison is derived globally and the upper one in the source block. -/
theorem PowerProfile.right_sampled_ordinary_weighted_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa d : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk : kappa < beta) (hd : 0 < d) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) < delta → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), ((h : ℝ)/(terminalDepth i : ℝ))^kappa*
      ((w n).rate i*((n : ℝ)/(h : ℝ))^beta/(h : ℝ))*
      Real.exp (-(d*((w n).rate i*((n : ℝ)/(h : ℝ))^beta)))) ≤ C := by
  obtain ⟨K, delta, hK, hdelta, hdelta1, hupper⟩ := hp.right_sampled_rate_upper
  obtain ⟨b, hb, hlower⟩ := hp.right_marked_rate_time_lower
  have hbeta : 0 < beta := hp.2.2.2.1.2.1
  obtain ⟨B, hB, hsum⟩ := right_ordinary_weighted_row_bound hbeta hk (mul_pos hd hb)
  refine ⟨K*B, delta, mul_pos hK hB, hdelta, hdelta1, ?_⟩
  intro grid w hw n i hi M
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hi0 : (0 : ℝ) < terminalDepth i := Nat.cast_pos.mpr (terminalDepth_pos i)
  have hir := (w n).positive i
  have hr := hupper grid w hw n i hi
  have hcompare : (∑ h ∈ Finset.Ico 1 (M+1), ((h : ℝ)/(terminalDepth i : ℝ))^kappa*
      ((w n).rate i*((n : ℝ)/(h : ℝ))^beta/(h : ℝ))*
      Real.exp (-(d*((w n).rate i*((n : ℝ)/(h : ℝ))^beta)))) ≤
    K*(∑ h ∈ Finset.Ico 1 (M+1), ((h : ℝ)/(terminalDepth i : ℝ))^kappa*
      (((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ))*
      Real.exp (-((d*b)*((terminalDepth i : ℝ)/(h : ℝ))^beta))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    have hhN : 0 < h := by have := (Finset.mem_Ico.mp hh).1; omega
    have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hhN
    have hl : b*((terminalDepth i : ℝ)/(h : ℝ))^beta ≤
        (w n).rate i*((n : ℝ)/(h : ℝ))^beta := by
      simpa only [mul_one, one_mul] using hlower grid w hw n i h 1 hhN zero_le_one
    have hu : (w n).rate i*((n : ℝ)/(h : ℝ))^beta ≤
        K*((terminalDepth i : ℝ)/(h : ℝ))^beta := by
      have he := mul_le_mul_of_nonneg_right hr
        (Real.rpow_nonneg (div_nonneg hn.le hhR.le) beta)
      have hid := right_power_time_identity (p := beta) hi0 hhR hn
      simpa only [mul_assoc, hid] using he
    exact weighted_rate_kernel_comparison (by positivity) hhR (by positivity)
      (by positivity) hK.le hd.le hl hu
  exact hcompare.trans (mul_le_mul_of_nonneg_left (hsum _ hi0 M) hK.le)

end Luce.Section6
