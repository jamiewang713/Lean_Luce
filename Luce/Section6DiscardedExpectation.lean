import Luce.Section6DiscardedCountRounding
import Luce.Section6RightDiscardedExpectation
import Luce.Section6LeftDiscardedExpectation

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Exact rounding transfers a uniform integer-cutoff estimate to all
real cutoffs. Empty rounded intervals have literal count zero. -/
theorem discarded_expectation_real_of_nat {n : ℕ} (w : Weights n)
    (side : Corner) (k : ℕ) {C delta : ℝ} (hC : 0 ≤ C)
    (hnat : ∀ A B : ℕ, 1 ≤ A → A ≤ B → (B : ℝ)/(n : ℝ) ≤ delta →
      (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) side k A B : ℝ)
        ∂exponentialRace w) ≤ C) (A B : ℝ) (hB : B/(n : ℝ) ≤ delta) :
    (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) side k A B : ℝ)
      ∂exponentialRace w) ≤ C := by
  have he : (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) side k A B : ℝ)
      ∂exponentialRace w) =
      ∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) side k
        (max 1 ⌈A⌉₊ : ℕ) (⌊B⌋₊ : ℕ) : ℝ) ∂exponentialRace w := by
    apply integral_congr_ae
    filter_upwards [] with clocks
    exact_mod_cast interval_discarded_count_rounding (raceRankPermutation clocks) side k A B
  rw [he]
  by_cases hAB : max 1 ⌈A⌉₊ ≤ ⌊B⌋₊
  · have hpos : 0 < ⌊B⌋₊ := (Nat.zero_lt_one.trans_le (le_max_left _ _)).trans_le hAB
    have hfloor : (⌊B⌋₊ : ℝ) ≤ B := (Nat.le_floor_iff' (Nat.ne_of_gt hpos)).mp le_rfl
    exact hnat _ _ (le_max_left _ _) hAB
      ((div_le_div_of_nonneg_right hfloor (Nat.cast_nonneg _)).trans hB)
  · have hlt : (⌊B⌋₊ : ℝ) < ((max 1 ⌈A⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_of_not_ge hAB
    simp only [interval_discarded_count_eq_zero_of_lt _ _ _ hlt, Nat.cast_zero, integral_zero]
    exact hC

/-- The manuscript's full right O(1) discarded-cycle expectation, for real
cutoffs and original profile/sampling inputs only. -/
theorem PowerProfile.right_discarded_expectation {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (k : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (A B : ℝ), B/(n : ℝ) ≤ delta →
      (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) .right k A B : ℝ)
        ∂exponentialRace (w n)) ≤ C := by
  obtain ⟨C, delta, hC, hd, hd1, hnat⟩ := hp.right_discarded_expectation_nat k
  refine ⟨C, delta, hC, hd, hd1, ?_⟩
  intro grid w hw n A B hB
  exact discarded_expectation_real_of_nat (w n) .right k hC.le
    (hnat grid w hw n) A B hB

/-- The manuscript's full left O(1) discarded-cycle expectation. All
cutoff conversion and generic probability premises are discharged. -/
theorem PowerProfile.left_discarded_expectation {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (k : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (A B : ℝ), B/(n : ℝ) ≤ delta →
      (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) .left k A B : ℝ)
        ∂exponentialRace (w n)) ≤ C := by
  obtain ⟨C, delta, hC, hd, hd1, hnat⟩ := hp.left_discarded_expectation_nat k
  refine ⟨C, delta, hC, hd, hd1, ?_⟩
  intro grid w hw n A B hB
  exact discarded_expectation_real_of_nat (w n) .left k hC.le
    (hnat grid w hw n) A B hB

end Luce.Section6
