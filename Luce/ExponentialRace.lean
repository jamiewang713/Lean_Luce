import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Luce.Model
import Mathlib.Probability.Independence.Basic

/-!
# Independent exponential clocks and the rank integral

This file constructs the actual product probability measure of independent
exponential clocks. Conditioning on one coordinate is implemented using the
measure-preserving `piFinSuccAbove` equivalence and Tonelli's theorem.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

namespace Luce

/-- Joint law of the independent exponential clocks. -/
noncomputable def exponentialRace {n : ℕ} (w : Weights n) : Measure (Fin n → ℝ) :=
  Measure.pi fun i => expMeasure (w.rate i)

instance exponentialRace_isProbability {n : ℕ} (w : Weights n) :
    IsProbabilityMeasure (exponentialRace w) := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (w.rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  unfold exponentialRace
  infer_instance

/-- The one-dimensional exponential survival function. -/
lemma expMeasure_Ioi {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    expMeasure r (Set.Ioi t) = ENNReal.ofReal (Real.exp (-(r * t))) := by
  letI := isProbabilityMeasure_expMeasure hr
  have he : Real.exp (-(r * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hr.le ht))
  rw [← Set.compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _),
    measure_univ, ← ofReal_cdf, cdf_expMeasure_eq hr, if_pos ht]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr he), sub_sub_cancel]

/-- Evaluation of one coordinate has the prescribed exponential law. -/
lemma exponentialRace_eval {n : ℕ} (w : Weights n) (i : Fin n) :
    MeasurePreserving (Function.eval i) (exponentialRace w) (expMeasure (w.rate i)) := by
  letI : ∀ j, IsProbabilityMeasure (expMeasure (w.rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (w.positive j)
  exact measurePreserving_eval _ i

/-- The coordinate clocks are mutually independent. -/
lemma exponentialRace_independent {n : ℕ} (w : Weights n) :
    iIndepFun (fun i (clocks : Fin n → ℝ) => clocks i) (exponentialRace w) := by
  letI : ∀ j, IsProbabilityMeasure (expMeasure (w.rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (w.positive j)
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-- Exact survival probability of a coordinate. -/
lemma exponentialRace_survival {n : ℕ} (w : Weights n) (i : Fin n)
    (t : ℝ) (ht : 0 ≤ t) :
    exponentialRace w {clocks | t < clocks i} =
      ENNReal.ofReal (Real.exp (-(w.rate i * t))) := by
  calc
    _ = expMeasure (w.rate i) (Set.Ioi t) :=
      (exponentialRace_eval w i).measure_preimage measurableSet_Ioi.nullMeasurableSet
    _ = _ := expMeasure_Ioi (w.positive i) ht
/-- The `n` other clocks, indexed by deleting the distinguished label. -/
noncomputable def backgroundRace {n : ℕ} (w : Weights (n + 1)) (i : Fin (n + 1)) :
    Measure (Fin n → ℝ) :=
  Measure.pi fun j => expMeasure (w.rate (i.succAbove j))

instance backgroundRace_isProbability {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) : IsProbabilityMeasure (backgroundRace w i) := by
  letI : ∀ j, IsProbabilityMeasure (expMeasure (w.rate (i.succAbove j))) :=
    fun j => isProbabilityMeasure_expMeasure (w.positive _)
  unfold backgroundRace
  infer_instance

/-- Number of background clocks surviving at time `t`. -/
noncomputable def backgroundSurvivors {n : ℕ} (t : ℝ) (clocks : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter fun j => t < clocks j).card

lemma measurable_backgroundSurvivors {n : ℕ} :
    Measurable (fun z : ℝ × (Fin n → ℝ) => backgroundSurvivors z.1 z.2) := by
  classical
  simp only [backgroundSurvivors, Finset.card_filter]
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.ite
    (measurableSet_lt measurable_fst ((measurable_pi_apply j).comp measurable_snd))
    measurable_const

/-- The exact conditioning identity for any nonnegative measurable statistic
of one distinguished clock and its background. -/
theorem exponentialRace_disintegrate {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (g : ℝ × (Fin n → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ clocks, g (clocks i, fun j => clocks (i.succAbove j)) ∂exponentialRace w) =
      ∫⁻ t, exponentialPDF (w.rate i) t *
        (∫⁻ background, g (t, background) ∂backgroundRace w i) := by
  letI : ∀ j, IsProbabilityMeasure (expMeasure (w.rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (w.positive j)
  have he := (measurePreserving_piFinSuccAbove
    (fun j => expMeasure (w.rate j)) i).lintegral_comp hg
  change (∫⁻ clocks, g (clocks i, fun j => clocks (i.succAbove j))
    ∂exponentialRace w) = ∫⁻ z, g z ∂((expMeasure (w.rate i)).prod (backgroundRace w i)) at he
  rw [he, lintegral_prod _ hg.aemeasurable]
  change (∫⁻ t, (∫⁻ background, g (t, background) ∂backgroundRace w i)
    ∂volume.withDensity (exponentialPDF (w.rate i))) = _
  exact lintegral_withDensity_eq_lintegral_mul _ ((measurable_exponentialPDFReal _).ennreal_ofReal)
    hg.lintegral_prod_right'

/-- Equation `eq:rank-integral`, expressed as a nonnegative Lebesgue integral.
The event says exactly `m` other clocks ring after the candidate. For distinct
clocks this is rank `n + 1 - m`, by `raceRank_eq_iff_survivors`. -/
theorem rank_integral_survivors {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (m : ℕ) :
    exponentialRace w {clocks |
      backgroundSurvivors (clocks i) (fun j => clocks (i.succAbove j)) = m} =
      ∫⁻ t, exponentialPDF (w.rate i) t *
        backgroundRace w i {background | backgroundSurvivors t background = m} := by
  classical
  have hset : MeasurableSet {z : ℝ × (Fin n → ℝ) |
      backgroundSurvivors z.1 z.2 = m} := measurable_backgroundSurvivors (measurableSet_singleton m)
  have hg : Measurable ({z : ℝ × (Fin n → ℝ) | backgroundSurvivors z.1 z.2 = m}.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hset
  have h := exponentialRace_disintegrate w i
    ({z : ℝ × (Fin n → ℝ) | backgroundSurvivors z.1 z.2 = m}.indicator
      (fun _ => (1 : ℝ≥0∞))) hg
  have hc : Measurable (fun clocks : Fin (n + 1) → ℝ =>
      (clocks i, fun j => clocks (i.succAbove j))) :=
    (measurable_pi_apply i).prodMk (measurable_pi_iff.mpr fun j => measurable_pi_apply _)
  have hleft := lintegral_indicator_fun_one (μ := exponentialRace w) (hset.preimage hc)
  have hright (t : ℝ) := lintegral_indicator_fun_one (μ := backgroundRace w i)
    (hset.preimage (measurable_const.prodMk measurable_id :
      Measurable (fun background : Fin n → ℝ => (t, background))))
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_preimage] at h hleft hright
  rw [hleft] at h
  simpa only [hright, Set.preimage_ofPred_eq] using h

end Luce





