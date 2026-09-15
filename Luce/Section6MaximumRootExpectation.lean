import Luce.Section6EndpointCycleProbability
import Luce.Section6InteriorCycleProbability
import Luce.Section5MaximumRoot
import Luce.Section5BulkPointProbability

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- Literal unrooted cycle counting agrees with the largest-root indicator. -/
theorem cycle_count_at_maximum_eq_indicator {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (v : Fin n) :
    (Finset.univ.filter (fun c : ↥(Section5.cycleOrbits R k) =>
      Section5.cycleMaximum R k c = v)).card =
      if v ∈ Section5.maximumCycleRoots R k then 1 else 0 := by
  classical
  by_cases hv : v ∈ Section5.maximumCycleRoots R k
  · obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hv
    have he : Finset.univ.filter (fun d : ↥(Section5.cycleOrbits R k) =>
        Section5.cycleMaximum R k d = v) = {c} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hd
        exact Section5.cycleMaximum_injective R k (hd.trans hc.symm)
      · rintro rfl
        exact hc
    rw [he, Finset.card_singleton, if_pos hv]
  · have he : Finset.univ.filter (fun d : ↥(Section5.cycleOrbits R k) =>
        Section5.cycleMaximum R k d = v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      apply hv
      exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩
    rw [he, Finset.card_empty, if_neg hv]

/-- The expected indicator of being the unique largest root is bounded
by the actual probability of belonging to a cycle of the same length. -/
theorem maximum_root_expectation_le_cycle_probability {n : ℕ} (w : Weights n)
    (k : ℕ) (v : Fin n) :
    (∫ clocks, (if v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k then (1 : ℝ) else 0)
      ∂exponentialRace w) ≤
      (exponentialRace w).real {clocks |
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k+1} := by
  have hF : Measurable (fun clocks : Fin n → ℝ =>
      if v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k then (1 : ℕ) else 0) :=
    measurable_race_permutation_statistic (fun R => if v ∈ Section5.maximumCycleRoots R k then (1 : ℕ) else 0)
  have hm : MeasurableSet {clocks : Fin n → ℝ | v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k} := by
    simpa only [ite_eq_left_iff, zero_ne_one, imp_false, not_not] using
      measurableSet_eq_fun hF (measurable_const (a := (1 : ℕ)))
  have he : (∫ clocks, (if v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k then (1 : ℝ) else 0)
      ∂exponentialRace w) =
      (exponentialRace w).real {clocks | v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k} := by
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
      integral_indicator_const (μ := exponentialRace w) (1 : ℝ) hm
  rw [he]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro clocks hc
  exact ((Section5.mem_maximumCycleRoots_iff (raceRankPermutation clocks) k v).mp hc).1

theorem PowerProfile.right_maximum_root_expectation {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (k : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ v : Fin n, (terminalDepth v : ℝ)/(n : ℝ) ≤ delta →
      (∫ clocks, (if v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k then (1 : ℝ) else 0)
        ∂exponentialRace (w n)) ≤ C/(terminalDepth v : ℝ) := by
  obtain ⟨C, delta, hC, hd, hd1, hb⟩ := hp.right_cycle_vertex_probability k
  refine ⟨C, delta, hC, hd, hd1, ?_⟩
  intro grid w hw n v hv
  exact (maximum_root_expectation_le_cycle_probability (w n) k v).trans (hb grid w hw n v hv)

theorem PowerProfile.left_maximum_root_expectation {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (k : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ v : Fin n, ((v.val : ℝ)+1)/(n : ℝ) ≤ delta →
      (∫ clocks, (if v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k then (1 : ℝ) else 0)
        ∂exponentialRace (w n)) ≤ C/((v.val : ℝ)+1) := by
  obtain ⟨C, delta, hC, hd, hd1, hb⟩ := hp.left_cycle_vertex_probability k
  refine ⟨C, delta, hC, hd, hd1, ?_⟩
  intro grid w hw n v hv
  exact (maximum_root_expectation_le_cycle_probability (w n) k v).trans (hb grid w hw n v hv)

theorem PowerProfile.interior_maximum_root_expectation {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ v : Fin n, eps*(n : ℝ) ≤ (v.val : ℝ)+1 →
      (v.val : ℝ)+1 ≤ (1-eps)*(n : ℝ) →
      (∫ clocks, (if v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k then (1 : ℝ) else 0)
        ∂exponentialRace (w n)) ≤ C/(n : ℝ) := by
  obtain ⟨C, hC, hb⟩ := hp.interior_cycle_vertex_probability heps k
  refine ⟨C, hC, ?_⟩
  intro grid w hw n v hl hu
  exact (maximum_root_expectation_le_cycle_probability (w n) k v).trans (hb grid w hw n v hl hu)

end Luce.Section6
