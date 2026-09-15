import Luce.Section6GapProbabilityProduct

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- Exactly the marked positions assigned to the chosen gap. -/
abbrev GapCoordinates {r : ℕ} (q : Fin r → ℕ) (k : ℕ) := {a : Fin r // q a = k}

/-- The ordered region in its own coordinates; no unused clocks remain. -/
def gapSimplexRegion {n r : ℕ} (u : Fin r → Fin n) (q : Fin r → ℕ)
    (k : ℕ) (old : Fin n → ℝ) : Set (GapCoordinates q k → ℝ) :=
  {t | (∀ a, DeletedGapCount (Finset.univ.image u) old k (t a)) ∧ StrictMono t}

theorem measurableSet_gapSimplexRegion {n r : ℕ} (u : Fin r → Fin n)
    (q : Fin r → ℕ) (k : ℕ) (old : Fin n → ℝ) :
    MeasurableSet (gapSimplexRegion u q k old) := by
  unfold gapSimplexRegion
  apply MeasurableSet.inter
  · change MeasurableSet {t : GapCoordinates q k → ℝ | ∀ a,
      DeletedGapCount (Finset.univ.image u) old k (t a)}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    exact measurableSet_deletedGapCount (Finset.univ.image u) (fun _ => old) k
      (fun t : GapCoordinates q k → ℝ => t a) (fun _ => measurable_const) (measurable_pi_apply a)
  · change MeasurableSet {t : GapCoordinates q k → ℝ | ∀ a b, a < b → t a < t b}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    apply MeasurableSet.iInter
    intro b
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply b)

theorem gapSimplexRegion_preimage {n r : ℕ} (u : Fin r → Fin n)
    (q : Fin r → ℕ) (k : ℕ) (old : Fin n → ℝ) :
    (fun fresh : Fin n → ℝ => fun a : GapCoordinates q k => fresh (u a.val)) ⁻¹'
      gapSimplexRegion u q k old = {fresh | GapOrderedInsertion u q k old fresh} := by
  ext fresh
  constructor
  · rintro ⟨hc, ho⟩
    refine ⟨fun a ha => hc ⟨a, ha⟩, ?_⟩
    intro a b ha hb hab
    exact ho (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) hab
  · rintro ⟨hc, ho⟩
    refine ⟨fun a => hc a.val a.property, ?_⟩
    intro a b hab
    exact ho a.val b.val a.property b.property hab

/-- The exact marginal law of the clocks in a single gap block. -/
theorem gapCoordinates_map_law {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (k : ℕ) (hu : Injective u) :
    (exponentialRace w).map
      (fun fresh : Fin n → ℝ => fun a : GapCoordinates q k => fresh (u a.val)) =
      Measure.pi (fun a : GapCoordinates q k => expMeasure (w.rate (u a.val))) := by
  have hi : Injective (fun a : GapCoordinates q k => u a.val) :=
    hu.comp Subtype.val_injective
  have hind := (exponentialRace_independent w).precomp hi
  have hh := hind.map_fun_eq_pi_map
    (fun a => (measurable_pi_apply (u a.val)).aemeasurable)
  rw [hh]
  congr 1
  funext a
  exact (exponentialRace_eval w (u a.val)).map_eq

/-- Each per-gap mass equals the product exponential measure of the
ordered region in exactly its own coordinates. -/
theorem gapOrderedKernel_eq_simplex_measure {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (k : ℕ) (hu : Injective u)
    (old : Fin n → ℝ) :
    gapOrderedKernel w u q k old =
      (Measure.pi (fun a : GapCoordinates q k => expMeasure (w.rate (u a.val))))
        (gapSimplexRegion u q k old) := by
  rw [← gapCoordinates_map_law w u q k hu,
    Measure.map_apply (measurable_pi_lambda _ (fun a => measurable_pi_apply (u a.val)))
      (measurableSet_gapSimplexRegion u q k old), gapSimplexRegion_preimage]
  rfl

end Luce.Section6
