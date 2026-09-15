import Luce.Section6UniformCycleConstants
import Luce.Section6LogExcursionExpectation
import Luce.Section6RegularCycleBounds
import Luce.Section6ActiveCycleBounds

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem selected_root_singleton67 {n : ℕ} (p : Equiv.Perm (Fin n))
    (k : ℕ) (v : Fin n) :
    selectedRootCycleCount p k {v} =
      if v ∈ Section5.maximumCycleRoots p k then 1 else 0 := by
  classical
  have he : selectedRootCycleCount p k {v} =
      (Finset.univ.filter fun c : ↥(Section5.cycleOrbits p k) =>
        Section5.cycleMaximum p k c = v).card := by
    apply congrArg Finset.card
    ext c
    simp
  rw [he]
  exact cycle_count_at_maximum_eq_indicator p k v

theorem PowerProfile.endpoint_estimates67 {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (k : ℕ) (side : Corner) :
    ∃ C delta q : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧ 0 < q ∧
      ((cornerBehavior left right side).active →
        Lemma67Contract.endpointEstimates f k side C delta q) := by
  obtain ⟨C, d, hC, hd, hd1, hroot⟩ := hp.active_root_bounds k side
  obtain ⟨D, e, hD, he, he1, hdisc⟩ := hp.active_discarded_bounds k side
  obtain ⟨E, t, q, hE, ht, ht1, hq, hlog⟩ := hp.active_log_expectation k side
  let delta := min d (min e t)
  have hdd : delta ≤ d := min_le_left _ _
  have hde : delta ≤ e := (min_le_right _ _).trans (min_le_left _ _)
  have hdt : delta ≤ t := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C+D+E, delta, q, by positivity, lt_min hd (lt_min he ht),
    hdd.trans_lt hd1, hq, ?_⟩
  intro ha grid w hw
  refine ⟨?_, ?_, ?_⟩
  · intro n v hv
    have hh := hroot ha grid w hw n v (hv.trans hdd)
    have heq : (∫ clocks, (selectedRootCycleCount (raceRankPermutation clocks) k {v} : ℝ)
        ∂exponentialRace (w n)) =
        ∫ clocks, (if v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k then (1 : ℝ) else 0)
          ∂exponentialRace (w n) := by
      apply integral_congr_ae
      filter_upwards [] with clocks
      exact_mod_cast selected_root_singleton67 (raceRankPermutation clocks) k v
    rw [heq]
    exact hh.trans (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  · intro n A B _hA _hAB hB
    exact (hdisc ha grid w hw n A B (hB.trans hde)).trans (by linarith)
  · intro n A B R hA hAB hB hR
    have hh := hlog ha grid w hw n A B R hA hAB (hB.trans hdt) hR
    have hAr : 0 < A := by linarith
    have hfactor : 0 ≤ 1+Real.log (B/A) := by
      have := Real.log_nonneg ((one_le_div hAr).mpr hAB)
      linarith
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hfactor) (by positivity))

theorem lemma67_active : Lemma67Contract.active := by
  intro f left right hp L
  let P : (Fin L × Corner) → ℝ → ℝ → ℝ → Prop := fun z C d q =>
    (cornerBehavior left right z.2).active →
      Lemma67Contract.endpointEstimates f z.1.val z.2 C d q
  obtain ⟨C, d, q, hC, hd, hd1, hq, hP⟩ := finite_uniform_cycle_constants P
    (fun z => hp.endpoint_estimates67 z.1.val z.2) (by
      intro z C d q C' d' q' hC hC' _hd' _hq' hCC hdd hqq h ha
      exact endpointEstimates_mono67 hC hC' hCC hdd hqq (h ha))
  refine ⟨C, d, q, hC, hd, hd1, hq, ?_⟩
  intro k hk side ha
  exact hP (⟨k, hk⟩, side) ha

theorem lemma67_regular : Lemma67Contract.regular := by
  intro f left right hp L eps he he1
  exact hp.off_active_root_expectation L he he1

/-- Full Lemma 6.7: uniform root, interval-exit and logarithmic-excursion
bounds at every active corner, plus the middle/inactive contribution.
No additional hypotheses or axioms are introduced. -/
theorem lemma67 : Lemma67Contract.lemma67 :=
  ⟨lemma67_active, lemma67_regular⟩

end Luce.Section6
