import Luce.Section6WeightedKernelComparison
import Luce.Section6LeftWeightedRate
import Luce.Section6RateTimeLower

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- The ordinary same-corner left weighted row for the actual sampled rates.
Both rate comparisons are derived from the original power profile. -/
theorem PowerProfile.left_sampled_ordinary_weighted_row {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta kappa d : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hk : kappa < alpha) (hd : 0 < d) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), ((i.val : ℝ)+1)/(n : ℝ) < delta → ∀ M : ℕ,
    (∑ h ∈ Finset.Ico 1 (M+1), (((i.val : ℝ)+1)/(h : ℝ))^kappa*
      ((w n).rate i*((h : ℝ)/(n : ℝ))^alpha/(h : ℝ))*
      Real.exp (-(d*((w n).rate i*((h : ℝ)/(n : ℝ))^alpha)))) ≤ C := by
  obtain ⟨K, hK, hupper⟩ := hp.global_left_sampled_power_upper
  obtain ⟨delta, hdelta, hdelta1, hlower⟩ := hp.left_marked_rate_time_lower
  have hc : 0 < c/2 := half_pos hp.2.2.1.1
  have ha : 0 < alpha := zero_lt_one.trans hp.2.2.1.2.1
  obtain ⟨B, hB, hsum⟩ := left_ordinary_weighted_row_bound ha hk (mul_pos hd hc)
  refine ⟨K*B, delta, mul_pos hK hB, hdelta, hdelta1, ?_⟩
  intro grid w hw n i hi M
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hi0 : 0 < (i.val : ℝ)+1 := by positivity
  have hir := (w n).positive i
  have hr := hupper grid w hw n i
  have hcompare : (∑ h ∈ Finset.Ico 1 (M+1), (((i.val : ℝ)+1)/(h : ℝ))^kappa*
      ((w n).rate i*((h : ℝ)/(n : ℝ))^alpha/(h : ℝ))*
      Real.exp (-(d*((w n).rate i*((h : ℝ)/(n : ℝ))^alpha)))) ≤
    K*(∑ h ∈ Finset.Ico 1 (M+1), (((i.val : ℝ)+1)/(h : ℝ))^kappa*
      (((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ))*
      Real.exp (-((d*(c/2))*((h : ℝ)/((i.val : ℝ)+1))^alpha))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    have hhN : 0 < h := by have := (Finset.mem_Ico.mp hh).1; omega
    have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hhN
    have hl : (c/2)*((h : ℝ)/((i.val : ℝ)+1))^alpha ≤
        (w n).rate i*((h : ℝ)/(n : ℝ))^alpha := by
      simpa only [mul_one, one_mul] using hlower grid w hw n i h 1 hhN zero_le_one hi
    have hu : (w n).rate i*((h : ℝ)/(n : ℝ))^alpha ≤
        K*((h : ℝ)/((i.val : ℝ)+1))^alpha := by
      have he := mul_le_mul_of_nonneg_right hr
        (Real.rpow_nonneg (div_nonneg hhR.le hn.le) alpha)
      have hid := left_power_time_identity (p := alpha) hi0 hhR hn
      simpa only [mul_assoc, hid] using he
    exact weighted_rate_kernel_comparison (by positivity) hhR (by positivity)
      (by positivity) hK.le hd.le hl hu
  exact hcompare.trans (mul_le_mul_of_nonneg_left (hsum _ hi0 M) hK.le)

end Luce.Section6
