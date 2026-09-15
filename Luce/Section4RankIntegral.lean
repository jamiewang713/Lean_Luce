import Luce.Section4ExponentialRace
import Luce.Section1RaceOrder
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The rank integral in a common probability space -/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

namespace Luce

/-- Counting background survivors is equivalent to erasing the candidate from
one common full-clock survivor set. -/
lemma backgroundSurvivors_eq_erase {n : ℕ} (clocks : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) :
    backgroundSurvivors t (fun j => clocks (i.succAbove j)) =
      ((survivorSet clocks t).erase i).card := by
  classical
  have hs := Fin.sum_univ_succAbove (fun j => if t < clocks j then (1 : ℕ) else 0) i
  have hc : (survivorSet clocks t).card =
      (if t < clocks i then 1 else 0) +
        backgroundSurvivors t (fun j => clocks (i.succAbove j)) := by
    simpa only [survivorSet, backgroundSurvivors, Finset.card_filter] using hs
  by_cases hi : t < clocks i
  · rw [Finset.card_erase_of_mem (by simp [survivorSet, hi])]
    simp only [if_pos hi] at hc
    omega
  · rw [Finset.erase_eq_of_notMem (by simp [survivorSet, hi])]
    simpa only [if_neg hi, zero_add] using hc.symm

lemma exponentialRace_background {n : ℕ} (w : Weights (n + 1)) (i : Fin (n + 1)) :
    MeasurePreserving (fun clocks : Fin (n + 1) → ℝ => fun j => clocks (i.succAbove j))
      (exponentialRace w) (backgroundRace w i) := by
  letI : ∀ j, IsProbabilityMeasure (expMeasure (w.rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (w.positive j)
  exact measurePreserving_snd.comp
    (measurePreserving_piFinSuccAbove (fun j => expMeasure (w.rate j)) i)

/-- The probability used in the rank integral can be evaluated in the common
full race, which permits the deterministic two-candidate estimate. -/
lemma background_probability_eq_common {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (t : ℝ) (m : ℕ) :
    backgroundRace w i {background | backgroundSurvivors t background = m} =
      exponentialRace w {clocks | ((survivorSet clocks t).erase i).card = m} := by
  have hb : MeasurableSet {background : Fin n → ℝ | backgroundSurvivors t background = m} :=
    (measurable_backgroundSurvivors.comp (measurable_const.prodMk measurable_id))
      (measurableSet_singleton m)
  have h := (exponentialRace_background w i).measure_preimage hb.nullMeasurableSet
  simpa only [Set.preimage_ofPred_eq, backgroundSurvivors_eq_erase] using h.symm

/-- The exact rank integral as an ordinary real-valued integral. The density
`exponentialPDFReal` vanishes at all negative times. -/
theorem rank_integral_real {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (m : ℕ) :
    (exponentialRace w).real {clocks |
      backgroundSurvivors (clocks i) (fun j => clocks (i.succAbove j)) = m} =
      ∫ t, exponentialPDFReal (w.rate i) t *
        (backgroundRace w i).real {background | backgroundSurvivors t background = m} := by
  classical
  let P : ℝ → ℝ≥0∞ := fun t =>
    backgroundRace w i {background | backgroundSurvivors t background = m}
  have hset : MeasurableSet {z : ℝ × (Fin n → ℝ) |
      backgroundSurvivors z.1 z.2 = m} := measurable_backgroundSurvivors (measurableSet_singleton m)
  have hP : Measurable P := by
    have h := (measurable_const.indicator hset : Measurable
      ({z : ℝ × (Fin n → ℝ) | backgroundSurvivors z.1 z.2 = m}.indicator
        (fun _ => (1 : ℝ≥0∞)))).lintegral_prod_right' (ν := backgroundRace w i)
    have hi (t : ℝ) := lintegral_indicator_fun_one (μ := backgroundRace w i)
      (hset.preimage (measurable_const.prodMk measurable_id :
        Measurable (fun background : Fin n → ℝ => (t, background))))
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_preimage] at h hi
    simpa only [hi, Set.preimage_ofPred_eq] using h
  have hm : AEStronglyMeasurable (fun t => exponentialPDFReal (w.rate i) t * (P t).toReal)
      volume := ((measurable_exponentialPDFReal _).mul hP.ennreal_toReal).aestronglyMeasurable
  have hn : 0 ≤ᵐ[volume] fun t => exponentialPDFReal (w.rate i) t * (P t).toReal :=
    Filter.Eventually.of_forall fun t => mul_nonneg
      (exponentialPDFReal_nonneg (w.positive i) t) ENNReal.toReal_nonneg
  change _ = ∫ t, exponentialPDFReal (w.rate i) t * (P t).toReal
  rw [integral_eq_lintegral_of_nonneg_ae hn hm]
  simp only [P, ENNReal.ofReal_mul (exponentialPDFReal_nonneg (w.positive i) _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact congrArg ENNReal.toReal (rank_integral_survivors w i m)

/-- The real rank integral evaluated entirely on one common exponential race. -/
theorem rank_integral_common {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (m : ℕ) :
    (exponentialRace w).real {clocks |
      ((survivorSet clocks (clocks i)).erase i).card = m} =
      ∫ t, exponentialPDFReal (w.rate i) t *
        (exponentialRace w).real {clocks | ((survivorSet clocks t).erase i).card = m} := by
  simpa only [backgroundSurvivors_eq_erase, measureReal_def,
    background_probability_eq_common] using rank_integral_real w i m

end Luce

