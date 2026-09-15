import Luce.Section6SampledRateUpper
import Luce.Section6RightRateFloor

noncomputable section
namespace Luce.Section6

/-- Every sampled rate has polynomial growth in the row size. This is a
consequence of the original profile, not a restriction on the rate array. -/
theorem PowerProfile.sampled_rate_polynomial_upper {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right) :
    ∃ K a : ℝ, 0 < K ∧ 0 ≤ a ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), (w n).rate i ≤ K*(n : ℝ)^a := by
  cases left with
  | finite c =>
    obtain ⟨M, hM, hb⟩ := hp.global_upper_of_left_finite
    refine ⟨M, 0, hM, le_refl 0, ?_⟩
    intro grid w hw n i
    simpa [hw n i] using hb (samplePoint grid n i) (samplePoint_mem grid i)
  | power c alpha eta =>
    obtain ⟨K, delta, hK, hd, hd1, hb⟩ := hp.left_sampled_rate_upper
    obtain ⟨M, hM, hoff⟩ := hp.upper_away_left (half_pos hd) (by linarith)
    have ha : 0 ≤ alpha := le_of_lt (lt_trans zero_lt_one hp.2.2.1.2.1)
    refine ⟨K+M, alpha, add_pos hK hM, ha, ?_⟩
    intro grid w hw n i
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
    have hp1 : 1 ≤ (n : ℝ)^alpha := Real.one_le_rpow hn1 ha
    by_cases hi : ((i.val : ℝ)+1)/(n : ℝ) < delta
    · have hr : (((i.val : ℝ)+1)/(n : ℝ))^(-alpha) ≤ (n : ℝ)^alpha := by
        have ht := Real.rpow_le_rpow_of_nonpos (one_div_pos.mpr hn)
          (div_le_div_of_nonneg_right (by have := Nat.cast_nonneg (α := ℝ) i.val; linarith : (1 : ℝ) ≤ (i.val : ℝ)+1) hn.le)
          (neg_nonpos.mpr ha)
        simpa [Real.rpow_neg_eq_inv_rpow, one_div] using ht
      calc
        (w n).rate i ≤ K*((((i.val : ℝ)+1)/(n : ℝ))^(-alpha)) := hb grid w hw n i hi
        _ ≤ K*(n : ℝ)^alpha := mul_le_mul_of_nonneg_left hr hK.le
        _ ≤ (K+M)*(n : ℝ)^alpha := by nlinarith
    · have hs := samplePoint_ge_half_label grid i
      have hs0 : delta/2 ≤ samplePoint grid n i := by push Not at hi; linarith
      have hm := hoff (samplePoint grid n i) ⟨hs0, (samplePoint_mem grid i).2⟩
      rw [hw n i]
      calc
        f (samplePoint grid n i) ≤ M := hm
        _ ≤ (K+M)*(n : ℝ)^alpha := by nlinarith

end Luce.Section6
