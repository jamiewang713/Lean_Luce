import Luce.Section6PositivePowerInversion

noncomputable section
namespace Luce.Section6

/-- Uniform inversion of an arrival population in the joint regime x
small and N*x large. The unknown quantile's small-time bound is derived. -/
theorem monotone_positive_power_quantile_error {A p q K : ℝ}
    (hA : 0 < A) (hp : 0 < p) (hq : 0 < q) (hK : 0 < K) :
    ∃ C delta M : ℝ, 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ N : ℝ, 0 < N → ∀ G : ℝ → ℝ, Monotone G →
      (∀ s : ℝ, 0 < s → s ≤ 1 → |G s-A*s^p| ≤ K*(s^(p+q)+1/N)) →
    ∀ x t : ℝ, 0 < x → x < delta → M ≤ N*x → 0 < t → G t = x →
      |t/(x/A)^(1/p)-1| ≤ C*(x^(q/p)+1/(N*x)) := by
  obtain ⟨C, hC, herror⟩ := positive_power_inverse_estimate hA hp hq hK
  let S := min (1/2 : ℝ) ((A/(8*K))^(1/q))
  have hbase : 0 < A/(8*K) := by positivity
  have hS : 0 < S := lt_min (by norm_num) (Real.rpow_pos_of_pos hbase _)
  have hS1 : S ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hSmall : K*S^q ≤ A/4 := by
    have hh := Real.rpow_le_rpow hS.le (min_le_right (1/2 : ℝ) ((A/(8*K))^(1/q))) hq.le
    rw [← Real.rpow_mul hbase.le, show (1/q)*q = (1 : ℝ) by field_simp, Real.rpow_one] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hK.le
    have hid : K*(A/(8*K)) = A/8 := by field_simp
    rw [hid] at hh'
    linarith
  refine ⟨C, A*S^p/4, 4*K+1, hC, by positivity, by positivity, ?_⟩
  intro N hN G hmono hbound x t hx hxsmall hlarge ht hquantile
  have hdisc : K/N ≤ x/4 := by
    apply (div_le_iff₀ hN).mpr
    nlinarith
  have hGS := hbound S hS hS1
  have hs := mul_le_mul_of_nonneg_left hSmall (Real.rpow_pos_of_pos hS p).le
  have hGS' : |G S-A*S^p| ≤ A*S^p/4+x/4 := by
    calc
      _ ≤ K*(S^(p+q)+1/N) := hGS
      _ = S^p*(K*S^q)+K/N := by rw [Real.rpow_add hS]; ring
      _ ≤ S^p*(A/4)+x/4 := add_le_add hs hdisc
      _ = _ := by ring
  have hAbove : x < G S := by
    have hh := abs_le.mp hGS'
    linarith [hh.1, hxsmall, hx]
  have htS : t < S := by
    by_contra hle
    have hh := hmono (le_of_not_gt hle)
    rw [hquantile] at hh
    exact (not_lt_of_ge hh) hAbove
  apply herror N x t hN hx ht
  · rw [← hquantile]
    exact hbound t ht (htS.le.trans hS1)
  · have hh := Real.rpow_le_rpow ht.le htS.le hq.le
    exact (mul_le_mul_of_nonneg_left hh hK.le).trans hSmall
  · exact hdisc

end Luce.Section6
