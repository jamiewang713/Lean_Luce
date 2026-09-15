import Luce.Section3RaceDrawLaw
import Luce.Section2PredictableProbability
import Luce.Section2FiniteAdaptedBernoulli

/-!
# The actual interior fixed points as an adapted Bernoulli row

This bridges the race proved in Section 3 with the predictable Poisson
criterion of Section 2. The conditional probabilities are proved from the
full Luce masses and are not supplied as a field of an assumed process.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set

namespace Luce

/-- The exact draw history, as a filtration on the exponential-clock space. -/
def raceDrawFiltration (n : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (Fin n → ℝ)) where
  seq := drawHistory raceDraw
  mono' := by
    intro a b hab
    unfold drawHistory
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    exact le_iSup_of_le j (le_iSup_of_le (lt_of_lt_of_le hj hab) le_rfl)
  le' := drawHistory_le raceDraw (measurable_raceDraw n)

/-- The fixed-point indicators restricted to the paper's interior window.
Spatial masking is deterministic, so the original draw history is retained. -/
def raceInteriorBernoulli {n : ℕ} (w : Weights n) (α : ℝ) :
    FiniteAdaptedBernoulli (exponentialRace w) n where
  filtration := raceDrawFiltration n
  observation k clocks := decide (((k.val : ℝ) + 1) / n ≤ α ∧ raceDraw clocks k = k)
  adapted k := by
    have htest : @Measurable (Fin n) Bool ⊤ inferInstance
        (fun i => decide (((k.val : ℝ) + 1) / n ≤ α ∧ i = k)) := fun _ _ => trivial
    exact htest.comp (measurable_draw_of_lt raceDraw k (Nat.lt_succ_self k.val))

/-- The Bool representation is exactly the source's real indicator,
including the one-based coordinate and the inverse-permutation convention. -/
theorem raceInteriorBernoulli_observation {n : ℕ} (w : Weights n) (α : ℝ)
    (k : Fin n) (clocks : Fin n → ℝ) :
    (raceInteriorBernoulli w α).observationReal k clocks =
      if ((k.val : ℝ) + 1) / n ≤ α then
        (if (raceDraw clocks).symm k = k then 1 else 0) else 0 := by
  classical
  simp only [FiniteAdaptedBernoulli.observationReal, raceInteriorBernoulli,
    decide_eq_true_eq, inverse_fixed_iff]
  split_ifs <;> simp_all

/-- The exact conditional-probability identification required to invoke
the predictable Poisson criterion for the interior fixed-point process. -/
theorem raceInteriorBernoulli_probability {n : ℕ} (w : Weights n) (α : ℝ) (k : Fin n) :
    (raceInteriorBernoulli w α).probability k =ᵐ[exponentialRace w]
      (fun clocks => if ((k.val : ℝ) + 1) / n ≤ α then
        predictableChance w (raceDraw clocks) k else 0) := by
  classical
  have hbase := (raceInteriorBernoulli w α).probability_ae_eq_condExp k
  by_cases hα : ((k.val : ℝ) + 1) / n ≤ α
  · have hobs : (raceInteriorBernoulli w α).observationReal k =
        fun clocks => if (raceDraw clocks).symm k = k then (1 : ℝ) else 0 := by
      funext clocks
      rw [raceInteriorBernoulli_observation, if_pos hα]
    rw [hobs] at hbase
    have hcond := predictable_fixed_point_probability (exponentialRace w) w raceDraw
      (measurable_raceDraw n) (raceDraw_mass w) k
    exact (hbase.trans hcond).mono fun clocks hc => by
      simpa only [if_pos hα, predictableChance_formula] using hc
  · have hobs : (raceInteriorBernoulli w α).observationReal k = 0 := by
      funext clocks
      rw [raceInteriorBernoulli_observation, if_neg hα]
      rfl
    rw [hobs, condExp_zero] at hbase
    exact hbase.mono fun clocks hc => by simpa only [if_neg hα, Pi.zero_apply] using hc

end Luce
