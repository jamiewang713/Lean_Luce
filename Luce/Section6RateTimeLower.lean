import Luce.Section6LeftRateFloor
import Luce.Section6RightRateFloor

noncomputable section
namespace Luce.Section6

theorem left_power_time_identity {a h n p : ℝ} (ha : 0 < a) (hh : 0 < h) (hn : 0 < n) :
    (a/n)^(-p)*(h/n)^p = (h/a)^p := by
  rw [Real.rpow_neg (div_nonneg ha.le hn.le), inv_mul_eq_div,
    ← Real.div_rpow (div_nonneg hh.le hn.le) (div_nonneg ha.le hn.le)]
  congr 1
  field_simp [ne_of_gt hn]

theorem right_power_time_identity {a h n p : ℝ} (ha : 0 < a) (hh : 0 < h) (hn : 0 < n) :
    (a/n)^p*(n/h)^p = (a/h)^p := by
  rw [← Real.mul_rpow (div_nonneg ha.le hn.le) (div_nonneg hn.le hh.le)]
  congr 1
  field_simp [ne_of_gt hn]

theorem PowerProfile.left_marked_rate_time_lower {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n) (h : ℕ) (k : ℝ), 0 < h → 0 ≤ k →
    ((i.val : ℝ)+1)/(n : ℝ) < delta →
      (c/2)*k*(((h : ℝ)/((i.val : ℝ)+1))^alpha) ≤
        (w n).rate i*(k*((h : ℝ)/(n : ℝ))^alpha) := by
  obtain ⟨delta, hd, hd1, hfloor⟩ := hp.left_initial_block_rate_floor
  refine ⟨delta, hd, hd1, ?_⟩
  intro grid w hw n i h k hh hk hi
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have haR : 0 < (i.val : ℝ)+1 := by positivity
  have hf := hfloor grid w hw n (i.val+1) hn (by simpa using hi) i (le_refl _)
  simp only [Nat.cast_add, Nat.cast_one] at hf
  have hb := mul_le_mul_of_nonneg_right hf
    (mul_nonneg hk (Real.rpow_nonneg (div_nonneg hhR.le hnR.le) alpha))
  have he : (c/2)*(((i.val : ℝ)+1)/(n : ℝ))^(-alpha)*(k*((h : ℝ)/(n : ℝ))^alpha) =
      (c/2)*k*((h : ℝ)/((i.val : ℝ)+1))^alpha := by
    calc
      _ = (c/2)*k*((((i.val : ℝ)+1)/(n : ℝ))^(-alpha)*((h : ℝ)/(n : ℝ))^alpha) := by ring
      _ = _ := by rw [left_power_time_identity haR hhR hnR]
  exact he ▸ hb

theorem PowerProfile.right_marked_rate_time_lower {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n) (h : ℕ) (k : ℝ), 0 < h → 0 ≤ k →
      C*k*(((terminalDepth i : ℝ)/(h : ℝ))^beta) ≤
        (w n).rate i*(k*((n : ℝ)/(h : ℝ))^beta) := by
  obtain ⟨C, hC, hfloor⟩ := hp.right_sampled_rate_floor
  refine ⟨C, hC, ?_⟩
  intro grid w hw n i h k hh hk
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have haR : (0 : ℝ) < terminalDepth i := Nat.cast_pos.mpr (terminalDepth_pos i)
  have hb := mul_le_mul_of_nonneg_right (hfloor grid w hw n i)
    (mul_nonneg hk (Real.rpow_nonneg (div_nonneg hnR.le hhR.le) beta))
  have he : C*((terminalDepth i : ℝ)/(n : ℝ))^beta*(k*((n : ℝ)/(h : ℝ))^beta) =
      C*k*((terminalDepth i : ℝ)/(h : ℝ))^beta := by
    calc
      _ = C*k*(((terminalDepth i : ℝ)/(n : ℝ))^beta*((n : ℝ)/(h : ℝ))^beta) := by ring
      _ = _ := by rw [right_power_time_identity haR hhR hnR]
  exact he ▸ hb

end Luce.Section6
