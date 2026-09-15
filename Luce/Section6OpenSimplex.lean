import Luce.Section6OpenGaps

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- The manuscript's ordered simplex inside the actual open deleted gap. -/
def openGapSimplexRegion {n r : ℕ} (u : Fin r → Fin n) (q : Fin r → ℕ)
    (k : ℕ) (old : Fin n → ℝ) (hold : Injective old) : Set (GapCoordinates q k → ℝ) :=
  {t | (∀ a, t a ∈ openOrderGap (compactDeletedClocks (Finset.univ.image u) old)
      (compactDeletedClocks_injective (Finset.univ.image u) old hold) k) ∧ StrictMono t}

theorem gapSimplexRegion_ae_eq_open {n r : ℕ} (u : Fin r → Fin n)
    (q : Fin r → ℕ) (k : ℕ) (old : Fin n → ℝ) (hold : Injective old)
    (hpos : ∀ i, 0 ≤ old i) :
    gapSimplexRegion u q k old =ᵐ[Measure.pi (fun _ : GapCoordinates q k => (volume : Measure ℝ))]
      openGapSimplexRegion u q k old hold := by
  have havoid : ∀ᵐ t ∂Measure.pi (fun _ : GapCoordinates q k => (volume : Measure ℝ)),
      ∀ a : GapCoordinates q k, ∀ i : Fin n, t a ≠ old i := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro i
    exact Measure.ae_eval_ne (fun _ : GapCoordinates q k => (volume : Measure ℝ)) a (old i)
  filter_upwards [havoid] with t ht
  apply propext
  change ((∀ a, DeletedGapCount (Finset.univ.image u) old k (t a)) ∧ StrictMono t) ↔
    ((∀ a, t a ∈ openOrderGap (compactDeletedClocks (Finset.univ.image u) old)
      (compactDeletedClocks_injective (Finset.univ.image u) old hold) k) ∧ StrictMono t)
  apply and_congr _ Iff.rfl
  apply forall_congr'
  intro a
  have hh := mem_openOrderGap_iff_count (compactDeletedClocks (Finset.univ.image u) old)
    (compactDeletedClocks_injective (Finset.univ.image u) old hold)
    (fun i => hpos _) k (t a) (fun i => ht a _)
  rw [clockBeforeCount_compactDeletedClocks] at hh
  exact hh.symm

/-- Literal real density integral in the open order-statistic simplex. -/
def openGapSimplexIntegral {n r : ℕ} (w : Weights n) (u : Fin r → Fin n)
    (q : Fin r → ℕ) (k : ℕ) (old : Fin n → ℝ) (hold : Injective old) : ℝ :=
  ∫ t in openGapSimplexRegion u q k old hold,
    ∏ a : GapCoordinates q k, w.rate (u a.val)*Real.exp (-(w.rate (u a.val)*t a))
    ∂Measure.pi (fun _ : GapCoordinates q k => (volume : Measure ℝ))

theorem gapSimplexIntegral_eq_open {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (k : ℕ)
    (old : Fin n → ℝ) (hold : Injective old) (hpos : ∀ i, 0 ≤ old i) :
    gapSimplexIntegral w u q k old = openGapSimplexIntegral w u q k old hold :=
  setIntegral_congr_set (gapSimplexRegion_ae_eq_open u q k old hold hpos)

theorem openGapSimplexIntegral_integrable {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (k : ℕ) (hu : Injective u)
    (old : Fin n → ℝ) (hold : Injective old) (hpos : ∀ i, 0 ≤ old i) :
    IntegrableOn (fun t => ∏ a : GapCoordinates q k,
      w.rate (u a.val)*Real.exp (-(w.rate (u a.val)*t a))) (openGapSimplexRegion u q k old hold)
      (Measure.pi (fun _ : GapCoordinates q k => (volume : Measure ℝ))) :=
  (gapSimplexIntegral_integrable_and_eq w u q k hu old).1.congr_set_ae
    (gapSimplexRegion_ae_eq_open u q k old hold hpos).symm

end Luce.Section6
