import Luce.RankIntegral
import Luce.ExponentialFacts
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # The paper's rank probability integral -/

open MeasureTheory ProbabilityTheory Set

namespace Luce

lemma exponentialPDFReal_eq_piecewise (r t : ℝ) :
    exponentialPDFReal r t = if 0 ≤ t then r * Real.exp (-r * t) else 0 := by
  simp [exponentialPDFReal, gammaPDFReal, neg_mul]

/-- Restricting the density integral to positive times gives the familiar
exponential density. -/
lemma integral_exponentialPDFReal (r : ℝ) (P : ℝ → ℝ) :
    (∫ t, exponentialPDFReal r t * P t) =
      ∫ t in Ioi 0, r * Real.exp (-r * t) * P t := by
  calc
    _ = ∫ t, (Ici (0 : ℝ)).indicator (fun t => r * Real.exp (-r * t) * P t) t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        simp only [exponentialPDFReal_eq_piecewise, Set.indicator_apply, Set.mem_Ici]
        split_ifs <;> simp
    _ = ∫ t in Ici 0, r * Real.exp (-r * t) * P t := integral_indicator measurableSet_Ici
    _ = _ := by rw [restrict_Ioi_eq_restrict_Ici]

/-- Conditioning on the distinguished exponential clock gives the exact
rank probability, for any requested one-based rank `r`. -/
theorem raceRank_probability_integral {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n + 1) :
    (exponentialRace w).real {clocks | raceRank clocks i = r} =
      ∫ t in Ioi 0, w.rate i * Real.exp (-w.rate i * t) *
        (exponentialRace w).real
          {clocks | ((survivorSet clocks t).erase i).card = n + 1 - r} := by
  have he : {clocks | raceRank clocks i = r} =ᵐ[exponentialRace w]
      {clocks | ((survivorSet clocks (clocks i)).erase i).card = n + 1 - r} := by
    filter_upwards [exponentialRace_injective_ae w] with clocks hc
    apply propext
    change raceRank clocks i = r ↔ ((survivorSet clocks (clocks i)).erase i).card = n + 1 - r
    have hi : i ∉ survivorSet clocks (clocks i) := by simp [survivorSet]
    simpa only [Set.mem_ofPred_eq, Finset.erase_eq_of_notMem hi] using
      raceRank_eq_iff_survivors clocks hc i r hr hrn
  calc
    _ = (exponentialRace w).real
        {clocks | ((survivorSet clocks (clocks i)).erase i).card = n + 1 - r} := by
      exact congrArg ENNReal.toReal (measure_congr he)
    _ = ∫ t, exponentialPDFReal (w.rate i) t *
        (exponentialRace w).real
          {clocks | ((survivorSet clocks t).erase i).card = n + 1 - r} :=
      rank_integral_common w i _
    _ = _ := integral_exponentialPDFReal _ _

/-- Equation `eq:rank-integral`, for the fixed-point event of label `i+1`. -/
theorem fixed_point_probability_integral {n : ℕ} (w : Weights (n + 1))
    (i : Fin (n + 1)) :
    (exponentialRace w).real {clocks | raceRank clocks i = i.val + 1} =
      ∫ t in Ioi 0, w.rate i * Real.exp (-w.rate i * t) *
        (exponentialRace w).real
          {clocks | ((survivorSet clocks t).erase i).card = n - i.val} := by
  simpa only [Nat.add_sub_add_right] using
    raceRank_probability_integral w i (i.val + 1) (by omega) (by omega)

end Luce

