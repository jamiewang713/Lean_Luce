import Luce.Section7Probability

/-! # Exact rank integrals for independent clocks with densities -/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

namespace Luce.Section7
noncomputable section

lemma background_probability {n : ℕ} (g : Fin (n + 1) → ClockDensity)
    (i : Fin (n + 1)) (t : ℝ) (m : ℕ) :
    clockRace (fun j => g (i.succAbove j)) {e | backgroundSurvivors t e = m} =
      clockRace g {e | otherSurvivors e i t = m} := by
  have hb : MeasurableSet {e : Fin n → ℝ | backgroundSurvivors t e = m} :=
    (measurable_backgroundSurvivors.comp (measurable_const.prodMk measurable_id))
      (measurableSet_singleton m)
  have hp : MeasurePreserving
      (fun e : Fin (n + 1) → ℝ => fun j => e (i.succAbove j))
      (clockRace g) (clockRace (fun j => g (i.succAbove j))) :=
    measurePreserving_snd.comp
      (measurePreserving_piFinSuccAbove (fun j => (g j).law) i)
  have h := hp.measure_preimage hb.nullMeasurableSet
  simpa only [Set.preimage_ofPred_eq, backgroundSurvivors_eq_erase,
    otherSurvivors_eq_erase] using h.symm

theorem clockRace_disintegrate {n : ℕ} (g : Fin (n + 1) → ClockDensity)
    (i : Fin (n + 1)) (f : ℝ × (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ e, f (e i, fun j => e (i.succAbove j)) ∂clockRace g) =
      ∫⁻ t, ENNReal.ofReal ((g i).density t) *
        (∫⁻ e, f (t, e) ∂clockRace (fun j => g (i.succAbove j))) := by
  have he := (measurePreserving_piFinSuccAbove (fun j => (g j).law) i).lintegral_comp hf
  change (∫⁻ e, f (e i, fun j => e (i.succAbove j)) ∂clockRace g) =
    ∫⁻ z, f z ∂((g i).law.prod (clockRace (fun j => g (i.succAbove j)))) at he
  rw [he, lintegral_prod _ hf.aemeasurable]
  exact lintegral_withDensity_eq_lintegral_mul _ (g i).measurable.ennreal_ofReal
    hf.lintegral_prod_right'

theorem rank_integral_survivors {n : ℕ} (g : Fin (n + 1) → ClockDensity)
    (i : Fin (n + 1)) (m : ℕ) :
    clockRace g {e | otherSurvivors e i (e i) = m} =
      ∫⁻ t, ENNReal.ofReal ((g i).density t) *
        clockRace g {e | otherSurvivors e i t = m} := by
  classical
  have hset : MeasurableSet {z : ℝ × (Fin n → ℝ) |
      backgroundSurvivors z.1 z.2 = m} :=
    measurable_backgroundSurvivors (measurableSet_singleton m)
  have h := clockRace_disintegrate g i
    ({z : ℝ × (Fin n → ℝ) | backgroundSurvivors z.1 z.2 = m}.indicator
      (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hset)
  have hc : Measurable (fun e : Fin (n + 1) → ℝ =>
      (e i, fun j => e (i.succAbove j))) :=
    (measurable_pi_apply i).prodMk (measurable_pi_iff.mpr fun j => measurable_pi_apply _)
  have hleft := lintegral_indicator_fun_one (μ := clockRace g) (hset.preimage hc)
  have hright (t : ℝ) := lintegral_indicator_fun_one
    (μ := clockRace (fun j => g (i.succAbove j)))
    (hset.preimage (measurable_const.prodMk measurable_id :
      Measurable (fun e : Fin n → ℝ => (t, e))))
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_preimage] at h hleft hright
  rw [hleft] at h
  simpa only [hright, Set.preimage_ofPred_eq, background_probability,
    backgroundSurvivors_eq_erase, ← otherSurvivors_eq_erase] using h

/-- Integrability follows from domination by the candidate's density. -/
theorem rank_integrand_integrable {n : ℕ} (g : Fin n → ClockDensity)
    (i : Fin n) (m : ℕ) :
    Integrable (fun t => (g i).density t * survivorProbability g i m t) := by
  apply (g i).integrable.mono'
    ((g i).measurable.mul (measurable_survivorProbability g i m)).aestronglyMeasurable
  filter_upwards [] with t
  change ‖(g i).density t * survivorProbability g i m t‖ ≤ (g i).density t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ((g i).nonneg t)
    (show 0 ≤ survivorProbability g i m t from measureReal_nonneg))]
  exact mul_le_of_le_one_right ((g i).nonneg t) measureReal_le_one

lemma rankOf_eq_raceRank {n : ℕ} (e : Fin n → ℝ) (i : Fin n) :
    rankOf e i = raceRank e i := by
  classical
  simp only [rankOf, raceRank, Finset.filter_erase]
  rw [Finset.erase_eq_of_notMem (by simp)]

/-- The conditioning identity in the proof of Proposition 7.1. -/
theorem clockRace_rank_integral {n : ℕ} (g : Fin n → ClockDensity)
    (i : Fin n) (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    (clockRace g).real {e | rankOf e i = r} =
      ∫ t, (g i).density t * survivorProbability g i (n - r) t := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have he : {e | rankOf e i = r} =ᵐ[clockRace g]
        {e | otherSurvivors e i (e i) = n + 1 - r} := by
      filter_upwards [clockRace_injective_ae g] with e hi
      apply propext
      change rankOf e i = r ↔ otherSurvivors e i (e i) = n + 1 - r
      have hnot : i ∉ survivorSet e (e i) := by simp [survivorSet]
      simpa only [Set.mem_ofPred_eq, rankOf_eq_raceRank, otherSurvivors_eq_erase,
        Finset.erase_eq_of_notMem hnot] using raceRank_eq_iff_survivors e hi i r hr hrn
    rw [show (clockRace g).real {e | rankOf e i = r} =
        (clockRace g).real {e | otherSurvivors e i (e i) = n + 1 - r} from
      congrArg ENNReal.toReal (measure_congr he)]
    rw [integral_eq_lintegral_of_nonneg_ae
      (f := fun t => (g i).density t * survivorProbability g i (n + 1 - r) t)
      (Filter.Eventually.of_forall fun t => mul_nonneg ((g i).nonneg t)
        (show 0 ≤ survivorProbability g i (n + 1 - r) t from measureReal_nonneg))
      (rank_integrand_integrable g i (n + 1 - r)).aestronglyMeasurable]
    simp only [survivorProbability, measureReal_def, ENNReal.ofReal_mul ((g i).nonneg _),
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact congrArg ENNReal.toReal (rank_integral_survivors g i _)

/-- The same exact identity on an arbitrary probability space. -/
theorem general_clock_rank_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (g : Fin n → ClockDensity)
    (T : Fin n → Ω → ℝ) (hLaw : ∀ i, HasLaw (T i) (g i).law P)
    (hIndependent : iIndepFun T P) (i : Fin n) (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    P.real {ω | rankOf (fun j => T j ω) i = r} =
      ∫ t, (g i).density t *
        P.real {ω | otherSurvivors (fun j => T j ω) i t = n - r} := by
  have hj : HasLaw (fun ω i => T i ω) (clockRace g) P :=
    hIndependent.hasLaw_pi hLaw
  have he : P.real {ω | rankOf (fun j => T j ω) i = r} =
      (clockRace g).real {e | rankOf e i = r} :=
    hj.measureReal_eq ((measurable_rankOf i) (measurableSet_singleton r))
  rw [he, clockRace_rank_integral g i r hr hrn]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  exact (hj.measureReal_eq (((measurable_otherSurvivors i).comp
    (measurable_const.prodMk measurable_id)) (measurableSet_singleton _))).symm

end
end Luce.Section7
