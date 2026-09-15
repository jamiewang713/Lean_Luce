import Luce.Section6SampledRateUpper
import Luce.Section6OutsideSourceRates

noncomputable section
namespace Luce.Section6

/-- The left power envelope holds at every source label, with a derived
constant also covering sources outside the asymptotic left block. -/
theorem PowerProfile.global_left_sampled_power_upper {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n),
      (w n).rate i ≤ K*((((i.val : ℝ)+1)/(n : ℝ))^(-alpha)) := by
  obtain ⟨B, delta, hB, hd, hd1, hb⟩ := hp.left_sampled_rate_upper
  obtain ⟨R, hR, hr⟩ := hp.sampled_upper_outside_left hd hd1
  refine ⟨B+R, add_pos hB hR, ?_⟩
  intro grid w hw n i
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hx : 0 < ((i.val : ℝ)+1)/(n : ℝ) := by positivity
  have hx1 : ((i.val : ℝ)+1)/(n : ℝ) ≤ 1 := by
    apply (div_le_one hn).mpr
    exact_mod_cast (show i.val+1 ≤ n by omega)
  have ha : 0 ≤ alpha := (zero_lt_one.trans hp.2.2.1.2.1).le
  have hpow : 1 ≤ (((i.val : ℝ)+1)/(n : ℝ))^(-alpha) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (neg_nonpos.mpr ha)
  by_cases hi : ((i.val : ℝ)+1)/(n : ℝ) < delta
  · have he := hb grid w hw n i hi
    nlinarith
  · have he := hr grid w hw n i (le_of_not_gt hi)
    nlinarith

/-- The weighted earliest-gap rate factor is uniformly bounded for every
source. No boundedness hypothesis is imposed on the rate family. -/
theorem PowerProfile.left_weighted_rate_bound {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n) (kappa : ℝ), kappa ≤ alpha →
      ((i.val : ℝ)+1)^kappa*((w n).rate i/(n : ℝ)^alpha) ≤ K := by
  obtain ⟨K, hK, hb⟩ := hp.global_left_sampled_power_upper
  refine ⟨K, hK, ?_⟩
  intro grid w hw n i kappa hk
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have ha1 : 1 ≤ (i.val : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) i.val; linarith
  have ha : 0 < (i.val : ℝ)+1 := zero_lt_one.trans_le ha1
  have hi := (w n).positive i
  have he := hb grid w hw n i
  have hid : ((i.val : ℝ)+1)^alpha*
      (K*((((i.val : ℝ)+1)/(n : ℝ))^(-alpha))/(n : ℝ)^alpha) = K := by
    rw [Real.div_rpow ha.le hn.le, Real.rpow_neg ha.le, Real.rpow_neg hn.le]
    have haP := (Real.rpow_pos_of_pos ha alpha).ne'
    have hnP := (Real.rpow_pos_of_pos hn alpha).ne'
    field_simp
  calc
    _ ≤ ((i.val : ℝ)+1)^alpha*((w n).rate i/(n : ℝ)^alpha) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ha1 hk) (by positivity)
    _ ≤ ((i.val : ℝ)+1)^alpha*
        (K*((((i.val : ℝ)+1)/(n : ℝ))^(-alpha))/(n : ℝ)^alpha) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he (by positivity)) (by positivity)
    _ = K := hid

end Luce.Section6
