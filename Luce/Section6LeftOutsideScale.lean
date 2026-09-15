import Luce.Section6OutsideSourceRates

noncomputable section
namespace Luce.Section6

/-- With the same cutoff for sources and targets, the rate-time scale is
uniformly bounded. Its bound need not be less than one. -/
theorem PowerProfile.left_outside_scaled_rate_bounded {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ B : ℝ, 0 < B ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n h : ℕ) (i : Fin n), (h : ℝ)/(n : ℝ) ≤ eps →
      eps ≤ ((i.val : ℝ)+1)/(n : ℝ) →
      (w n).rate i*((h : ℝ)/(n : ℝ))^alpha ≤ B := by
  obtain ⟨M, hM, hb⟩ := hp.sampled_upper_outside_left heps heps1
  have ha : 0 < alpha := lt_trans zero_lt_one hp.2.2.1.2.1
  refine ⟨M*eps^alpha, mul_pos hM (Real.rpow_pos_of_pos heps _), ?_⟩
  intro grid w hw n h i hh hi
  have hx : 0 ≤ (h : ℝ)/(n : ℝ) := by positivity
  exact (mul_le_mul_of_nonneg_right (hb grid w hw n i hi) (Real.rpow_nonneg hx _)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hh ha.le) hM.le)

/-- A smaller left target block makes the rate-time scale less than one
for every source outside the fixed left source block. Thus this region
does not require an extreme-rate remainder. -/
theorem PowerProfile.left_outside_scaled_rate_small {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n h : ℕ) (i : Fin n), (h : ℝ)/(n : ℝ) ≤ delta →
      eps ≤ ((i.val : ℝ)+1)/(n : ℝ) →
      (w n).rate i*((h : ℝ)/(n : ℝ))^alpha < 1 := by
  obtain ⟨M, hM, hb⟩ := hp.sampled_upper_outside_left heps heps1
  have ha : 0 < alpha := lt_trans zero_lt_one hp.2.2.1.2.1
  let t : ℝ := 1/(M+1)
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨min (1/2) (t^(1/alpha)), lt_min (by norm_num) (Real.rpow_pos_of_pos ht _),
    (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro grid w hw n h i hh hi
  have hx : 0 ≤ (h : ℝ)/(n : ℝ) := by positivity
  have hpow : ((h : ℝ)/(n : ℝ))^alpha ≤ t := by
    have he : (t^(1/alpha))^alpha = t := by
      rw [← Real.rpow_mul ht.le, one_div_mul_cancel ha.ne', Real.rpow_one]
    rw [← he]
    exact Real.rpow_le_rpow hx (hh.trans (min_le_right _ _)) ha.le
  have hrate := hb grid w hw n i hi
  calc
    _ ≤ M*((h : ℝ)/(n : ℝ))^alpha :=
      mul_le_mul_of_nonneg_right hrate (Real.rpow_nonneg hx _)
    _ ≤ M*t := mul_le_mul_of_nonneg_left hpow hM.le
    _ < 1 := by
      dsimp [t]
      rw [← div_eq_mul_one_div]
      exact (div_lt_one (by linarith : 0 < M+1)).mpr (by linarith)

end Luce.Section6
