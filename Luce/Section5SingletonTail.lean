import Luce.Section5CycleTailLimit
import Luce.Section4EndpointShellTightness

noncomputable section
open MeasureTheory Function Filter
namespace Luce

theorem singleton_cycle_tail_le_fixed {n : ℕ} (e : Fin n → ℝ)
    (hinj : Function.Injective e) (α : ℝ) :
    Section5.cycleCount (raceRankPermutation e) 0 -
      Section5.bulkCycleCount (raceRankPermutation e) α 0 ≤ tailFixedPointCount e α := by
  classical
  rw [Section5.tailCycleCount_eq_maximum_roots]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hroot, htail⟩ := Finset.mem_filter.mp hv
  have hp := (Section5.mem_maximumCycleRoots_iff (raceRankPermutation e) 0 v).mp hroot |>.1
  have hfixed : raceRankPermutation e v = v := by
    simpa only [Nat.zero_add, minimalPeriod_eq_one_iff_isFixedPt, IsFixedPt] using hp
  rw [raceRankPermutation_eq e hinj] at hfixed
  have hval := congrArg Fin.val hfixed
  change (clockRank e v).val = v.val at hval
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, htail, ?_⟩
  rw [rankOf_eq_raceRank_for_tail]
  simp only [clockRank] at hval
  simp only [raceRank, hval]
  omega

theorem cycleTailExpectation_zero_le (w : WeightArray) (n : ℕ) (α : ℝ) :
    cycleTailExpectation w 0 n α ≤
      ∫ e, (tailFixedPointCount e α : ℝ) ∂exponentialRace (w n) := by
  apply integral_mono_ae (integrable_race_permutation_statistic (w n)
    (fun R => ((Section5.cycleCount R 0 - Section5.bulkCycleCount R α 0 : ℕ) : ℝ)))
    (integrable_tailFixedPointCount (w n) α)
  filter_upwards [exponentialRace_injective_ae (w n)] with e he
  exact_mod_cast singleton_cycle_tail_le_fixed e he α

theorem EndpointShellAssumption.cycle_tail_small {w : WeightArray} {f : ℝ → ℝ}
    (hend : EndpointShellAssumption w) (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, α < 1 ∧ ∀ᶠ n : ℕ in atTop, cycleTailExpectation w k n α < ε := by
  cases k with
  | zero =>
    obtain ⟨α, _, hα, hrows⟩ := hend.expectation_tightness hnorm ε hε
    exact ⟨α, hα, hrows.mono (fun n hn => (cycleTailExpectation_zero_le w n α).trans_lt hn)⟩
  | succ k => exact hend.cycle_tail_small_succ hnorm hf k hε

end Luce
