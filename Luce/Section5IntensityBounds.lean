import Luce.Section5FactorialMoments
import Luce.Section5CycleShellTightness

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Luce

theorem bulk_cycle_count_le_total {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (α : ℝ) : Section5.bulkCycleCount R α k ≤ Section5.cycleCount R k := by
  rw [Section5.bulkCycleCount_eq_maximum_roots, ← Section5.maximumCycleRoots_card]
  exact Finset.card_filter_le _ _

theorem bulk_cycle_count_mono {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) : Monotone (fun α => Section5.bulkCycleCount R α k) := by
  intro α β h
  dsimp only
  rw [Section5.bulkCycleCount_eq_maximum_roots, Section5.bulkCycleCount_eq_maximum_roots]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hv, ha⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hv, ha.trans (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))⟩

theorem bulk_cycle_intensity_mono (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (k : ℕ) :
    MonotoneOn (fun α => bulkCycleTraceIntensity f α k) (Set.Iio 1) := by
  intro α hα β hβ h
  apply le_of_tendsto_of_tendsto (bulk_cycle_first_moment w f hnorm hf k α hα)
    (bulk_cycle_first_moment w f hnorm hf k β hβ)
  apply Eventually.of_forall
  intro n
  dsimp only
  apply integral_mono (integrable_race_permutation_statistic (w n)
    (fun R => (Section5.bulkCycleCount R α k : ℝ)))
    (integrable_race_permutation_statistic (w n) (fun R => (Section5.bulkCycleCount R β k : ℝ)))
  intro z
  exact Nat.cast_le.mpr (bulk_cycle_count_mono _ k h)

/-- The difference of two bulk expectations is bounded by the original
endpoint expectation, without exchanging any limits or assuming moments. -/
theorem bulk_expectation_sub_le_tail (w : WeightArray) (k n : ℕ) (α β : ℝ) :
    (∫ z, (Section5.bulkCycleCount (raceRankPermutation z) β k : ℝ) ∂exponentialRace (w n)) -
    (∫ z, (Section5.bulkCycleCount (raceRankPermutation z) α k : ℝ) ∂exponentialRace (w n)) ≤
      cycleTailExpectation w k n α := by
  have hi (a : ℝ) : Integrable (fun z =>
      (Section5.bulkCycleCount (raceRankPermutation z) a k : ℝ)) (exponentialRace (w n)) :=
    integrable_race_permutation_statistic (w n) (fun R => (Section5.bulkCycleCount R a k : ℝ))
  rw [← integral_sub (hi β) (hi α)]
  unfold cycleTailExpectation
  apply integral_mono ((hi β).sub (hi α))
    (integrable_race_permutation_statistic (w n)
      (fun R => ((Section5.cycleCount R k - Section5.bulkCycleCount R α k : ℕ) : ℝ)))
  intro z
  dsimp only [Pi.sub_apply]
  rw [Nat.cast_sub (bulk_cycle_count_le_total _ k α)]
  exact sub_le_sub_right (Nat.cast_le.mpr (bulk_cycle_count_le_total _ k β)) _

/-- The manuscript's uniform Cauchy estimate for truncated intensities.
The cutoff is selected from the raw shell condition before beta and n. -/
theorem EndpointShellAssumption.bulk_intensity_tail_small
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, α < 1 ∧ ∀ β : ℝ, β < 1 →
      bulkCycleTraceIntensity f β k - bulkCycleTraceIntensity f α k ≤ ε := by
  obtain ⟨α, hα, hrows⟩ := hend.cycle_tail_small hnorm hf k hε
  refine ⟨α, hα, fun β hβ => ?_⟩
  apply le_of_tendsto ((bulk_cycle_first_moment w f hnorm hf k β hβ).sub
    (bulk_cycle_first_moment w f hnorm hf k α hα))
  filter_upwards [hrows] with n hn
  exact (bulk_expectation_sub_le_tail w k n α β).trans hn.le

/-- Uniform boundedness of the literal truncated intensities is a proved
consequence of the shell condition, not a finiteness input. -/
theorem EndpointShellAssumption.bulk_intensity_bounded
    {w : WeightArray} {f : ℝ → ℝ} (hend : EndpointShellAssumption w)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f) (k : ℕ) :
    ∃ C : ℝ, ∀ α : ℝ, α < 1 → bulkCycleTraceIntensity f α k ≤ C := by
  obtain ⟨β, _, h⟩ := hend.bulk_intensity_tail_small hnorm hf k (ε := 1) zero_lt_one
  refine ⟨bulkCycleTraceIntensity f β k + 1, fun α hα => ?_⟩
  have := h α hα
  linarith

end Luce
