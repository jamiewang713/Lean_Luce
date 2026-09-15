import Luce.Section4ExponentialFacts
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Independent-copy resampling for Section 5

The coordinate swaps in `fixed_points.tex:1117–1123` are performed on the
actual product law of two independent copies of each clock. No exchangeability
of clocks with different rates is used: only the two copies of one label are
swapped. All event probabilities below are nonnegative extended measures.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Luce

/-- Independent pairs `(E_i^0,E_i^1)`, with the rate attached to label `i`. -/
def pairedExponentialRace {n : ℕ} (w : Weights n) :
    Measure (Fin n → ℝ × ℝ) :=
  Measure.pi fun i => (expMeasure (w.rate i)).prod (expMeasure (w.rate i))

instance pairedExponentialRace_isProbability {n : ℕ} (w : Weights n) :
    IsProbabilityMeasure (pairedExponentialRace w) := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (w.rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  unfold pairedExponentialRace
  infer_instance

/-- Swap only the prescribed labels, keeping every rate attached to its label. -/
def swapClockCopies {n : ℕ} (s : Finset (Fin n))
    (c : Fin n → ℝ × ℝ) (i : Fin n) : ℝ × ℝ :=
  if i ∈ s then (c i).swap else c i

theorem swapClockCopies_involutive {n : ℕ} (s : Finset (Fin n)) :
    Function.Involutive (swapClockCopies s) := by
  intro c
  funext i
  simp only [swapClockCopies]
  split_ifs <;> simp

/-- The law-preserving swaps used in the finite insertion proof, source
1117–1123. This statement uses the actual exponential product law. -/
theorem swapClockCopies_measurePreserving {n : ℕ} (w : Weights n)
    (s : Finset (Fin n)) :
    MeasurePreserving (swapClockCopies s)
      (pairedExponentialRace w) (pairedExponentialRace w) := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (w.rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  apply measurePreserving_pi _ _
    (f := fun i p => if i ∈ s then Prod.swap p else p)
  intro i
  by_cases hi : i ∈ s
  · simpa only [swapClockCopies, hi, if_true] using
      (Measure.measurePreserving_swap (μ := expMeasure (w.rate i))
        (ν := expMeasure (w.rate i)))
  · simp only [hi, if_false]
    exact ⟨measurable_id, Measure.map_id⟩

/-- The background projection is the original independent exponential race. -/
theorem pairedExponentialRace_background {n : ℕ} (w : Weights n) :
    MeasurePreserving (fun c : Fin n → ℝ × ℝ => fun i => (c i).1)
      (pairedExponentialRace w) (exponentialRace w) := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (w.rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  exact measurePreserving_pi _ _ (fun _ => measurePreserving_fst)

/-- Every fixed set of replacements again has the original race law. -/
theorem swapped_background_measurePreserving {n : ℕ} (w : Weights n)
    (s : Finset (Fin n)) :
    MeasurePreserving
      (fun c : Fin n → ℝ × ℝ => fun i => (swapClockCopies s c i).1)
      (pairedExponentialRace w) (exponentialRace w) :=
  (pairedExponentialRace_background w).comp (swapClockCopies_measurePreserving w s)

/-- The new background ranks form a permutation almost surely, for any
fixed replacement set. Distinctness is proved from the law, not assumed. -/
theorem swapped_background_injective_ae {n : ℕ} (w : Weights n)
    (s : Finset (Fin n)) :
    ∀ᵐ c ∂pairedExponentialRace w,
      Function.Injective (fun i => (swapClockCopies s c i).1) :=
  (swapped_background_measurePreserving w s).quasiMeasurePreserving.ae
    (exponentialRace_injective_ae w)

/-- Actual joint law of the two entire clock families. This permits Tonelli
to interpret the window product as a conditional probability. -/
theorem pairedExponentialRace_families {n : ℕ} (w : Weights n) :
    MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
      (pairedExponentialRace w) ((exponentialRace w).prod (exponentialRace w)) := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (w.rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (w.positive i)
  exact measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) _ _

end Luce
