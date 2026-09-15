import Luce.Section5CycleProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Counting vertices in short cycles

`shortCycleVertexCount` is the manuscript's `V_(n,L)(S)`: each vertex in
the specified set is counted once if its cycle has length at most `L`.
The exact expectation is a finite sum of vertex probabilities, and the
subsequent finite union bound keeps every length and every vertex explicit.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

/-- The number of vertices in `S` whose permutation cycle has length at
most `L`. Lengths are indexed by `Fin L` with the source's one-based shift. -/
def shortCycleVertexCount {n : ℕ} (R : Equiv.Perm (Fin n)) (L : ℕ)
    (S : Finset (Fin n)) : ℕ :=
  (S.filter fun v => ∃ k : Fin L, minimalPeriod (R : Fin n → Fin n) v = k.val + 1).card

/-- The `Fin L` representation is exactly the source condition that the
actual cycle length is at most `L`; finite permutations have positive period. -/
theorem shortCycleVertexCount_eq_filter_period_le {n : ℕ}
    (R : Equiv.Perm (Fin n)) (L : ℕ) (S : Finset (Fin n)) :
    shortCycleVertexCount R L S =
      (S.filter fun v => minimalPeriod (R : Fin n → Fin n) v ≤ L).card := by
  unfold shortCycleVertexCount
  congr 1
  apply Finset.filter_congr
  intro v _
  have hpos := minimalPeriod_pos_of_mem_periodicPts (R.injective.mem_periodicPts v)
  constructor
  · rintro ⟨k, hk⟩
    rw [hk]
    omega
  · intro hle
    refine ⟨⟨minimalPeriod (R : Fin n → Fin n) v - 1, by omega⟩, ?_⟩
    dsimp only
    omega

/-- Passing between draw order and rank order leaves every counted vertex
unchanged; this uses the proved equality of the two minimal periods. -/
theorem shortCycleVertexCount_inverse {n : ℕ}
    (R : Equiv.Perm (Fin n)) (L : ℕ) (S : Finset (Fin n)) :
    shortCycleVertexCount R.symm L S = shortCycleVertexCount R L S := by
  simp only [shortCycleVertexCount, Section5.minimalPeriod_symm]

lemma shortCycleVertexCount_le_card {n : ℕ} (R : Equiv.Perm (Fin n)) (L : ℕ)
    (S : Finset (Fin n)) : shortCycleVertexCount R L S ≤ S.card :=
  Finset.card_filter_le _ _

lemma shortCycleVertexCount_zero {n : ℕ} (R : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : shortCycleVertexCount R 0 S = 0 := by
  simp [shortCycleVertexCount]

lemma shortCycleVertexCount_empty {n : ℕ} (R : Equiv.Perm (Fin n)) (L : ℕ) :
    shortCycleVertexCount R L ∅ = 0 := by simp [shortCycleVertexCount]

lemma measurableSet_shortCycleVertex {n : ℕ} (L : ℕ) (v : Fin n) :
    MeasurableSet {clocks : Fin n → ℝ | ∃ k : Fin L,
      minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k.val + 1} := by
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun k => measurableSet_cycle_period v k.val)

/-- Measurability follows from a finite sum of measurable vertex indicators. -/
theorem measurable_shortCycleVertexCount {n : ℕ} (L : ℕ) (S : Finset (Fin n)) :
    Measurable (fun clocks : Fin n → ℝ =>
      shortCycleVertexCount (raceRankPermutation clocks) L S) := by
  have heq : (fun clocks : Fin n → ℝ => shortCycleVertexCount (raceRankPermutation clocks) L S) =
      (fun clocks => ∑ v ∈ S, if ∃ k : Fin L,
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k.val + 1
        then (1 : ℕ) else 0) := by
    funext clocks
    simp [shortCycleVertexCount, Finset.sum_boole]
  rw [heq]
  apply Finset.measurable_sum
  intro v _
  exact Measurable.ite (measurableSet_shortCycleVertex L v) measurable_const measurable_const

theorem shortCycleVertexCount_integrable {n : ℕ} (w : Weights n)
    (L : ℕ) (S : Finset (Fin n)) :
    Integrable (fun clocks => (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ))
      (exponentialRace w) := by
  apply Integrable.of_bound (((measurable_of_countable (fun r : ℕ => (r : ℝ))).comp
    (measurable_shortCycleVertexCount L S)).aestronglyMeasurable)
    (S.card : ℝ)
  apply Filter.Eventually.of_forall
  intro clocks
  change ‖(shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ)‖ ≤ (S.card : ℝ)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast shortCycleVertexCount_le_card (raceRankPermutation clocks) L S

/-- Exact vertex counting: the expectation is the sum of short-cycle
membership probabilities, with no multiplicity or symmetry factor. -/
theorem shortCycleVertexCount_expectation_eq {n : ℕ} (w : Weights n)
    (L : ℕ) (S : Finset (Fin n)) :
    (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ)
      ∂exponentialRace w) =
      ∑ v ∈ S, (exponentialRace w).real {clocks | ∃ k : Fin L,
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k.val + 1} := by
  have heq : (fun clocks : Fin n → ℝ =>
      (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ)) =
      (fun clocks => ∑ v ∈ S, if ∃ k : Fin L,
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k.val + 1
        then (1 : ℝ) else 0) := by
    funext clocks
    simp only [shortCycleVertexCount, Finset.sum_boole]
  rw [heq, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro v _
    simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] using
      (integral_indicator_one (μ := exponentialRace w) (measurableSet_shortCycleVertex L v))
  · intro v _
    have hi := (integrable_const (μ := exponentialRace w) (1 : ℝ)).indicator
      (measurableSet_shortCycleVertex L v)
    apply hi.congr
    exact Filter.Eventually.of_forall (fun clocks => by
      simp only [Set.indicator, Set.mem_ofPred_eq])

/-- The finite union bound over lengths, for arbitrary `S` and `L`, used
to pass from the single-vertex cycle estimate to `V_(n,L)(S)`. -/
theorem shortCycleVertexCount_expectation_le {n : ℕ} (w : Weights n)
    (L : ℕ) (S : Finset (Fin n)) :
    (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ)
      ∂exponentialRace w) ≤
      ∑ v ∈ S, ∑ k : Fin L, (exponentialRace w).real {clocks |
        minimalPeriod (raceRankPermutation clocks : Fin n → Fin n) v = k.val + 1} := by
  rw [shortCycleVertexCount_expectation_eq]
  apply Finset.sum_le_sum
  intro v _
  rw [Set.ofPred_exists]
  exact measureReal_iUnion_fintype_le _

/-- Combining the previous count with the proved ghost cycle comparison.
Every individual integral is justified by `ghostCycleVertexSum_integrable`. -/
theorem shortCycleVertexCount_expectation_le_ghost {n : ℕ} (w : Weights n)
    (L : ℕ) (S : Finset (Fin n)) :
    (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ)
      ∂exponentialRace w) ≤
      ∑ v ∈ S, ∑ k : Fin L,
        ∫ old, ghostCycleVertexSum w k.val v old ∂exponentialRace w := by
  apply (shortCycleVertexCount_expectation_le w L S).trans
  apply Finset.sum_le_sum
  intro v _
  exact Finset.sum_le_sum (fun k _ => cycle_vertex_probability_le_ghost w k.val v)

end Luce
