import Luce.Section3CompensatorLimit
import Luce.Section3LuceLaw

/-!
# Proposition 3.2 for every Luce-law permutation model

The exponential representation has been proved to have the exact full Luce
law. This transfers the compensator and maximum conclusions to the manuscript's
permutation model on arbitrary row probability spaces, with no clock or
coupling hypotheses. The test function has literally domain `[0,α]`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- All finite permutation events have the same probabilities under the
defining Luce law and the proved exponential-race representation. -/
theorem luce_event_probability {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ)
    (s : Set (Equiv.Perm (Fin n))) :
    P (π ⁻¹' s) = exponentialRace w (raceDraw ⁻¹' s) := by
  letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hs : MeasurableSet s := trivial
  rw [← Measure.map_apply hπ hs,
    luce_map_eq_raceDraw P w π hπ hMass,
    Measure.map_apply (measurable_raceDraw n) hs]

/-- The literal weighted predictable sum, in terms of the draw permutation
rather than a choice of an underlying clock representation. -/
def luceInteriorCompensatorSum {n : ℕ} (w : Weights n) (g : ℝ → ℝ)
    (α : ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∑ k : Fin n, if ((k.val : ℝ) + 1) / n ≤ α then
    g (((k.val : ℝ) + 1) / n) * predictableChance w π k else 0

lemma luceInteriorCompensatorSum_race {n : ℕ} (w : Weights n)
    (g : ℝ → ℝ) (α : ℝ) (clocks : Fin n → ℝ) :
    luceInteriorCompensatorSum w g α (raceDraw clocks) =
      interiorCompensatorSum w g α clocks := rfl

/-- Proposition 3.2, `eq:weighted-compensator`, on an arbitrary Luce-law
model. Every continuous test on the exact source interval is admitted.
Its total extension is proved to equal the original test on that interval. -/
theorem section3_weighted_compensator_luce
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ)
    {α : ℝ} (hα : α < 1) (g : Icc (0 : ℝ) α → ℝ) (hg : Continuous g) :
    ConvergesInProbability P
      (fun n ω => luceInteriorCompensatorSum (w n) (intervalTestExtension α g) α (π n ω))
      (∫ x in Ioc (0 : ℝ) α, intervalTestExtension α g x * profileDiagonal f x) := by
  intro ε hε
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hmeasure (n : ℕ) :
      (P (n + 1)).real {ω | ε <
        |luceInteriorCompensatorSum (w (n + 1)) (intervalTestExtension α g) α (π (n + 1) ω) -
          ∫ x in Ioc (0 : ℝ) α, intervalTestExtension α g x * profileDiagonal f x|} =
      (exponentialRace (w (n + 1))).real {clocks | ε <
        |interiorCompensatorSum (w (n + 1)) (intervalTestExtension α g) α clocks -
          ∫ x in Ioc (0 : ℝ) α, intervalTestExtension α g x * profileDiagonal f x|} := by
    exact congrArg ENNReal.toReal
      (luce_event_probability (P (n + 1)) (w (n + 1)) (π (n + 1))
        (hπ (n + 1)) (hMass (n + 1))
        {σ | ε < |luceInteriorCompensatorSum (w (n + 1)) (intervalTestExtension α g) α σ -
          ∫ x in Ioc (0 : ℝ) α, intervalTestExtension α g x * profileDiagonal f x|})
  simpa only [hmeasure] using
    (section3_weighted_compensator w f hnorm hf hα (intervalTestExtension α g)
      (continuousOn_intervalTestExtension α g hg) ε hε)

/-- Proposition 3.2, `eq:interior-max-p`, for every measurable permutation
having exactly the manuscript's Luce masses. -/
theorem section3_max_probability_luce
    (Ω : ℕ → Type*) [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (f : ℝ → ℝ) (hnorm : NormalizedWeights w)
    (hf : ProfileLimit w f) (π : ∀ n, Ω n → Equiv.Perm (Fin n))
    (hπ : ∀ n, @Measurable (Ω n) (Equiv.Perm (Fin n)) (mΩ n) ⊤ (π n))
    (hMass : ∀ n (σ : Equiv.Perm (Fin n)), (P n).real {ω | π n ω = σ} = (w n).mass σ)
    {α : ℝ} (hα : α < 1) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {ω | ∃ k : Fin n, ((k.val : ℝ) + 1) / n ≤ α ∧
        ε ≤ predictableChance (w n) (π n ω) k}) atTop (𝓝 0) := by
  intro ε hε
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hmeasure (n : ℕ) :
      P (n + 1) {ω | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        ε ≤ predictableChance (w (n + 1)) (π (n + 1) ω) k} =
      exponentialRace (w (n + 1)) {clocks | ∃ k : Fin (n + 1),
        ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        ε ≤ predictableChance (w (n + 1)) (raceDraw clocks) k} :=
    luce_event_probability (P (n + 1)) (w (n + 1)) (π (n + 1))
      (hπ (n + 1)) (hMass (n + 1))
      {σ | ∃ k : Fin (n + 1), ((k.val : ℝ) + 1) / (n + 1 : ℕ) ≤ α ∧
        ε ≤ predictableChance (w (n + 1)) σ k}
  simpa only [hmeasure] using section3_max_probability w f hnorm hf hα ε hε

end Luce
