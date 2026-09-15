import Luce.Section6DiscardedExpectation
import Luce.Section6MaximumRootExpectation

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Both endpoint cases, with inactive endpoints imposing no requirement. -/
theorem PowerProfile.active_root_bounds {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (k : ℕ) (side : Corner) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ((cornerBehavior left right side).active →
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (v : Fin n), (cornerDistance side v : ℝ)/(n : ℝ) ≤ delta →
      (∫ clocks, (if v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k then (1 : ℝ) else 0)
        ∂exponentialRace (w n)) ≤ C/(cornerDistance side v : ℝ)) := by
  cases side with
  | left =>
    cases left with
    | finite c => exact ⟨1, 1/2, by norm_num, by norm_num, by norm_num, by simp [cornerBehavior, EndpointBehavior.active]⟩
    | power c alpha eta =>
      obtain ⟨C, d, hC, hd, hd1, hb⟩ := hp.left_maximum_root_expectation k
      refine ⟨C, d, hC, hd, hd1, fun _ => ?_⟩
      simpa only [cornerDistance, Nat.cast_add, Nat.cast_one] using hb
  | right =>
    cases right with
    | finite c => exact ⟨1, 1/2, by norm_num, by norm_num, by norm_num, by simp [cornerBehavior, EndpointBehavior.active]⟩
    | power c beta eta =>
      obtain ⟨C, d, hC, hd, hd1, hb⟩ := hp.right_maximum_root_expectation k
      refine ⟨C, d, hC, hd, hd1, fun _ => ?_⟩
      simpa only [cornerDistance, terminalDepth] using hb

theorem PowerProfile.active_discarded_bounds {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (k : ℕ) (side : Corner) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ((cornerBehavior left right side).active →
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (A B : ℝ), B/(n : ℝ) ≤ delta →
      (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) side k A B : ℝ)
        ∂exponentialRace (w n)) ≤ C) := by
  cases side with
  | left =>
    cases left with
    | finite c => exact ⟨1, 1/2, by norm_num, by norm_num, by norm_num, by simp [cornerBehavior, EndpointBehavior.active]⟩
    | power c alpha eta =>
      obtain ⟨C, d, hC, hd, hd1, hb⟩ := hp.left_discarded_expectation k
      exact ⟨C, d, hC, hd, hd1, fun _ => hb⟩
  | right =>
    cases right with
    | finite c => exact ⟨1, 1/2, by norm_num, by norm_num, by norm_num, by simp [cornerBehavior, EndpointBehavior.active]⟩
    | power c beta eta =>
      obtain ⟨C, d, hC, hd, hd1, hb⟩ := hp.right_discarded_expectation k
      exact ⟨C, d, hC, hd, hd1, fun _ => hb⟩

end Luce.Section6
