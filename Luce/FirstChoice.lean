import Luce.RankProbability
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Ring

/-! # Proportional first choice in the exponential race -/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

namespace Luce

lemma backgroundSurvivors_eq_all {n : ℕ} (t : ℝ) (background : Fin n → ℝ) :
    backgroundSurvivors t background = n ↔ ∀ j, t < background j := by
  classical
  have hc := (Finset.univ.filter fun j => t < background j).card_eq_iff_eq_univ
  simp only [Fintype.card_fin] at hc
  rw [backgroundSurvivors, hc]
  simp [Finset.ext_iff]

/-- The probability that all background clocks survive is the product of
their exponential survival functions. -/
lemma background_all_probability {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (t : ℝ) (ht : 0 ≤ t) :
    (backgroundRace w i).real {background | backgroundSurvivors t background = n} =
      Real.exp (-(∑ j, w.rate (i.succAbove j)) * t) := by
  letI : ∀ j, IsProbabilityMeasure (expMeasure (w.rate (i.succAbove j))) :=
    fun j => isProbabilityMeasure_expMeasure (w.positive _)
  have he : {background : Fin n → ℝ | backgroundSurvivors t background = n} =
      Set.univ.pi (fun _ => Ioi t) := by
    ext background
    simp only [Set.mem_ofPred_eq, backgroundSurvivors_eq_all, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Ioi]
  rw [measureReal_def, he, backgroundRace, Measure.pi_pi]
  simp only [expMeasure_Ioi (w.positive _) ht, ENNReal.toReal_prod,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.sum_neg_distrib, ← Finset.sum_mul, neg_mul]

/-- A label wins an independent exponential race with probability equal to
its weight divided by the total weight, the Luce choice rule. -/
theorem exponentialRace_first_choice {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) :
    (exponentialRace w).real {clocks | raceRank clocks i = 1} =
      w.rate i / w.total Finset.univ := by
  have htotal : 0 < w.total Finset.univ := w.total_pos ⟨i, Finset.mem_univ _⟩
  rw [raceRank_probability_integral w i 1 (by omega) (by omega)]
  simp only [Nat.add_sub_cancel]
  calc
    (∫ t in Ioi 0, w.rate i * Real.exp (-w.rate i * t) *
        (exponentialRace w).real {clocks | ((survivorSet clocks t).erase i).card = n}) =
      ∫ t in Ioi 0, w.rate i * Real.exp (-w.total Finset.univ * t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [measureReal_def, ← background_probability_eq_common]
      change w.rate i * Real.exp (-w.rate i * t) *
        (backgroundRace w i).real {background | backgroundSurvivors t background = n} = _
      rw [background_all_probability w i t ht.le, mul_assoc, ← Real.exp_add]
      congr 2
      unfold Weights.total
      rw [Fin.sum_univ_succAbove (fun j => w.rate j) i]
      ring
    _ = w.rate i / w.total Finset.univ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos htotal)]
      simp [div_eq_mul_inv]

end Luce


