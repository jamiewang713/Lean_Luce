import Luce.Section6RightRateFloor
import Luce.Section6PositiveDepthSums

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- The deterministic right remaining-rate floor of `lem:sp-quantiles`.
It holds for every surviving set, so bounded deletions require no extra
assumption or separate probabilistic event. -/
theorem PowerProfile.right_remaining_rate_floor {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ remaining : Finset (Fin n),
      C*(n : ℝ)^(-beta)*(remaining.card : ℝ)^(beta+1) ≤
        ∑ i ∈ remaining, (w n).rate i := by
  classical
  have hb := h.2.2.2.1.2.1
  obtain ⟨C, hC, hfloor⟩ := h.right_sampled_rate_floor
  refine ⟨C/(beta+1), div_pos hC (by linarith), ?_⟩
  intro grid w hw n hn remaining
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let depths := remaining.image terminalDepth
  have hd : ∀ k ∈ depths, 0 < k := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact terminalDepth_pos i
  have hsum := positive_natset_rpow_sum_ge depths hd hb
  have hcard : depths.card = remaining.card := Finset.card_image_of_injective remaining (terminalDepth_injective n)
  have hsumEq : (∑ k ∈ depths, (k : ℝ)^beta) = ∑ i ∈ remaining, (terminalDepth i : ℝ)^beta := by
    exact Finset.sum_image (fun i _ j _ hij => terminalDepth_injective n hij)
  rw [hcard, hsumEq] at hsum
  have hcoef : 0 ≤ C/(n : ℝ)^beta := div_nonneg hC.le (Real.rpow_pos_of_pos hnR _).le
  calc
    _ = (C/(n : ℝ)^beta)*((remaining.card : ℝ)^(beta+1)/(beta+1)) := by
      rw [Real.rpow_neg hnR.le]
      ring
    _ ≤ (C/(n : ℝ)^beta)*(∑ i ∈ remaining, (terminalDepth i : ℝ)^beta) :=
      mul_le_mul_of_nonneg_left hsum hcoef
    _ = ∑ i ∈ remaining, C*((terminalDepth i : ℝ)/(n : ℝ))^beta := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.div_rpow (Nat.cast_nonneg _) hnR.le]
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hfloor grid w hw n i

end Luce.Section6
