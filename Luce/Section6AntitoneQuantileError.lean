import Luce.Section6NegativePowerInversion

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

/-- Uniform inversion in the joint regime x small and N*x large. All
smallness of the unknown quantile is proved from the population error
and monotonicity, rather than added as an input. -/
theorem antitone_negative_power_quantile_error {A p q K : ℝ}
    (hA : 0 < A) (hp : 0 < p) (hq : 0 < q) (hK : 0 < K) :
    ∃ C delta M : ℝ, 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ N : ℝ, 0 < N → ∀ H : ℝ → ℝ, Antitone H →
      (∀ s : ℝ, 1 ≤ s → |H s-A*s^(-p)| ≤ K*(s^(-(p+q))+1/N)) →
    ∀ x t : ℝ, 0 < x → x < delta → M ≤ N*x → 0 < t → H t = x →
      |t/(A/x)^(1/p)-1| ≤ C*(x^(q/p)+1/(N*x)) := by
  obtain ⟨C, hC, herror⟩ := negative_power_inverse_estimate hA hp hq hK
  have htend : Tendsto (fun s : ℝ => K*s^(-q)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hq).const_mul K
  have hev := htend.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < A/4))
  obtain ⟨S, hS1, hSmall⟩ := ((eventually_ge_atTop (1 : ℝ)).and hev).exists
  have hS : 0 < S := zero_lt_one.trans_le hS1
  refine ⟨C, A*S^(-p)/4, 4*K+1, hC, by positivity, by positivity, ?_⟩
  intro N hN H hmono hbound x t hx hxsmall hlarge ht hquantile
  have hdisc : K/N ≤ x/4 := by
    apply (div_le_iff₀ hN).mpr
    nlinarith
  have hHS := hbound S hS1
  have hprod : S^(-(p+q)) = S^(-p)*S^(-q) := by
    rw [← Real.rpow_add hS]
    congr 1
    ring
  have hs := mul_le_mul_of_nonneg_left hSmall.le (Real.rpow_pos_of_pos hS (-p)).le
  have hHS' : |H S-A*S^(-p)| ≤ A*S^(-p)/4+x/4 := by
    calc
      _ ≤ K*(S^(-(p+q))+1/N) := hHS
      _ = S^(-p)*(K*S^(-q))+K/N := by rw [hprod]; ring
      _ ≤ S^(-p)*(A/4)+x/4 := add_le_add hs hdisc
      _ = _ := by ring
  have hAbove : x < H S := by
    have hh := abs_le.mp hHS'
    linarith [hh.1, hxsmall, hx]
  have hSt : S < t := by
    by_contra hle
    have hh := hmono (le_of_not_gt hle)
    rw [hquantile] at hh
    exact (not_lt_of_ge hh) hAbove
  apply herror N x t hN hx ht
  · rw [← hquantile]
    exact hbound t (hS1.trans hSt.le)
  · have hh := Real.rpow_le_rpow_of_nonpos hS hSt.le (by linarith : -q ≤ 0)
    exact (mul_le_mul_of_nonneg_left hh hK.le).trans hSmall.le
  · exact hdisc

end Luce.Section6
