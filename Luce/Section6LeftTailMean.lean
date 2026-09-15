import Luce.Section6LeftMeanEnvelope

noncomputable section
namespace Luce.Section6

/-- Choose a fixed early-time multiple of (h/n)^alpha whose actual deleted
arrival mean is at most h/4. Deletion can only decrease the arrival mean. -/
theorem PowerProfile.left_early_deleted_mean {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ k H : ℝ, 0 < k ∧ k ≤ 1 ∧ 0 < H ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → 0 < h → h ≤ n → H ≤ (h : ℝ) →
    ∀ removed : Finset (Fin n),
      (n : ℝ)*deletedG (w n) removed (k*((h : ℝ)/(n : ℝ))^alpha) ≤ (h : ℝ)/4 := by
  obtain ⟨M, hM, hbound⟩ := hp.left_populationG_envelope
  have ha : 0 < alpha := by have := hp.2.2.1.2.1; linarith
  let u := min (1 : ℝ) (1/(8*M))
  have hu : 0 < u := lt_min zero_lt_one (one_div_pos.mpr (by positivity))
  have hu1 : u ≤ 1 := min_le_left _ _
  have hMu : M*u ≤ 1/8 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 8*M)).mp (min_le_right 1 (1/(8*M)))
    dsimp [u]
    nlinarith
  let k := u^alpha
  have hk : 0 < k := Real.rpow_pos_of_pos hu _
  have hk1 : k ≤ 1 := Real.rpow_le_one hu.le hu1 ha.le
  refine ⟨k, 8*M, hk, hk1, by positivity, ?_⟩
  intro grid w hw n h hn hh hhn hH removed
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hx : 0 < (h : ℝ)/(n : ℝ) := div_pos hhR hnR
  have hx1 : (h : ℝ)/(n : ℝ) ≤ 1 := (div_le_one hnR).mpr (Nat.cast_le.mpr hhn)
  have ht : 0 < k*((h : ℝ)/(n : ℝ))^alpha := mul_pos hk (Real.rpow_pos_of_pos hx _)
  have ht1 : k*((h : ℝ)/(n : ℝ))^alpha ≤ 1 := by
    have hb := mul_le_mul_of_nonneg_left (Real.rpow_le_one hx.le hx1 ha.le) hk.le
    calc
      _ ≤ k := by simpa only [mul_one] using hb
      _ ≤ 1 := hk1
  have htpow : (k*((h : ℝ)/(n : ℝ))^alpha)^(1/alpha) = u*((h : ℝ)/(n : ℝ)) := by
    dsimp [k]
    rw [← Real.mul_rpow hu.le hx.le, ← Real.rpow_mul (mul_nonneg hu.le hx.le),
      show alpha*(1/alpha) = 1 by field_simp [ne_of_gt ha], Real.rpow_one]
  calc
    _ ≤ (n : ℝ)*populationG (w n) (k*((h : ℝ)/(n : ℝ))^alpha) :=
      mul_le_mul_of_nonneg_left (deletedG_le_populationG (w n) removed ht.le) hnR.le
    _ ≤ (n : ℝ)*(M*((k*((h : ℝ)/(n : ℝ))^alpha)^(1/alpha)+1/(n : ℝ))) :=
      mul_le_mul_of_nonneg_left (hbound grid w hw n hn _ ht ht1) hnR.le
    _ = M*u*(h : ℝ)+M := by
      rw [htpow]
      field_simp [ne_of_gt hnR]
      <;> ring
    _ ≤ (h : ℝ)/4 := by nlinarith [mul_le_mul_of_nonneg_right hMu hhR.le]

end Luce.Section6
