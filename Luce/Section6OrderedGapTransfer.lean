import Luce.Section6JointGapMoment

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- Real expectation transfer on one order event, from the proved measure identity. -/
theorem ordered_gap_integral_transfer {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (H : (Fin n → ℝ) → ℝ) (hH : Measurable H) :
    (∫ c in {c | StrictMono (fun q => c (σ q))}, H (orderedNormalizedGaps w σ c)
      ∂exponentialRace w) = (w.mass σ)*(∫ ξ, H ξ ∂standardGapLaw n) := by
  rw [← integral_map (measurable_orderedNormalizedGaps w σ).aemeasurable hH.aestronglyMeasurable,
    exponentialRace_orderedNormalizedGaps, integral_smul_measure]
  simp [ENNReal.toReal_ofReal (w.mass_pos σ).le]

theorem ordered_gap_integrable_transfer {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (H : (Fin n → ℝ) → ℝ)
    (hH : Integrable H (standardGapLaw n)) :
    IntegrableOn (fun c => H (orderedNormalizedGaps w σ c))
      {c | StrictMono (fun q => c (σ q))} (exponentialRace w) := by
  have hi : Integrable H (((exponentialRace w).restrict
      {c | StrictMono (fun q => c (σ q))}).map (orderedNormalizedGaps w σ)) := by
    rw [exponentialRace_orderedNormalizedGaps]
    exact hH.smul_measure ENNReal.ofReal_ne_top
  exact (integrable_map_measure hi.aestronglyMeasurable
    (measurable_orderedNormalizedGaps w σ).aemeasurable).mp hi

/-- Moment reduction for the actual nonfinal race gap on each order event.
Both sides use the original clocks and measure; no gap-law premise is assumed. -/
theorem ordered_race_gap_moment_bound {n : ℕ} (w : Weights n)
    (σ : Equiv.Perm (Fin n)) (q : Fin n) {a : ℝ} (ha : 0 < a) (p : ℕ) :
    IntegrableOn (fun c => exponentialGapMass a (previousOrderedTime (fun l => c (σ l)) q)
      (c (σ q)-previousOrderedTime (fun l => c (σ l)) q)^p)
      {c | StrictMono (fun l => c (σ l))} (exponentialRace w) ∧
    (∫ c in {c | StrictMono (fun l => c (σ l))},
      exponentialGapMass a (previousOrderedTime (fun l => c (σ l)) q)
        (c (σ q)-previousOrderedTime (fun l => c (σ l)) q)^p ∂exponentialRace w) ≤
      (p.factorial : ℝ)*(a/orderedRemainingRate w σ q)^p*
      (∫ c in {c | StrictMono (fun l => c (σ l))},
        Real.exp (-((p : ℝ)*a*previousOrderedTime (fun l => c (σ l)) q)) ∂exponentialRace w) := by
  let H := fun ξ => exponentialGapMass a (gapStartFromNormalized w σ q ξ)
    (ξ q / orderedRemainingRate w σ q)^p
  let E := fun ξ => Real.exp (-((p : ℝ)*a*gapStartFromNormalized w σ q ξ))
  have hmH : Measurable H := by
    dsimp [H]
    unfold gapStartFromNormalized exponentialGapMass survivalKernel
    fun_prop
  have hmE : Measurable E := by
    dsimp [E]
    unfold gapStartFromNormalized
    fun_prop
  have heH (c : Fin n → ℝ) : H (orderedNormalizedGaps w σ c) =
      exponentialGapMass a (previousOrderedTime (fun l => c (σ l)) q)
        (c (σ q)-previousOrderedTime (fun l => c (σ l)) q)^p := by
    dsimp [H]
    rw [gapStartFromNormalized_eq_previous, ← ordered_gap_eq_normalized_div_rate]
  have heE (c : Fin n → ℝ) : E (orderedNormalizedGaps w σ c) =
      Real.exp (-((p : ℝ)*a*previousOrderedTime (fun l => c (σ l)) q)) := by
    dsimp [E]
    rw [gapStartFromNormalized_eq_previous]
  have hj := joint_gap_moment_bound w σ q ha p
  have hi := ordered_gap_integrable_transfer w σ H hj.1
  simp_rw [heH] at hi
  refine ⟨hi, ?_⟩
  have htH := ordered_gap_integral_transfer w σ H hmH
  have htE := ordered_gap_integral_transfer w σ E hmE
  simp_rw [heH] at htH
  simp_rw [heE] at htE
  rw [htH, htE]
  have hb := mul_le_mul_of_nonneg_left hj.2 (w.mass_pos σ).le
  dsimp [H, E]
  nlinarith only [hb]

end Luce.Section6
