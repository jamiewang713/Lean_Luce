import Luce.Section5DeletedGaps
import Luce.Section5GapMomentTransfer

/-! # Actual deleted-gap coefficients for Lemma 5.2

All time and rate functions are total measurable functions of the actual
background. Their values agree with the consecutive ordered gaps almost
surely, with the preceding time zero for the initial gap.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators

namespace Luce

def raceGapStart {n : ℕ} (c : Fin n → ℝ) (q : Fin n) : ℝ :=
  previousOrderedTime (fun k => c (raceDraw c k)) q

def raceGapRate {n : ℕ} (w : Weights n) (c : Fin n → ℝ) (q : Fin n) : ℝ :=
  orderedRemainingRate w (raceDraw c) q

lemma measurable_raceGapStart {n : ℕ} (q : Fin n) :
    Measurable (fun c : Fin n → ℝ => raceGapStart c q) := by
  let _ : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hm : Measurable (fun z : (Equiv.Perm (Fin n)) × (Fin n → ℝ) =>
      previousOrderedTime (fun k => z.2 (z.1 k)) q) := by
    apply measurable_from_prod_countable_right
    intro σ
    unfold previousOrderedTime
    split_ifs with hq
    · exact measurable_const
    · exact measurable_pi_apply (σ ⟨q.val - 1, by omega⟩)
  exact hm.comp ((measurable_raceDraw n).prodMk measurable_id)

lemma measurable_raceGapRate {n : ℕ} (w : Weights n) (q : Fin n) :
    Measurable (fun c : Fin n → ℝ => raceGapRate w c q) := by
  let _ : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hm : Measurable (fun σ : Equiv.Perm (Fin n) => orderedRemainingRate w σ q) :=
    Measurable.of_discrete
  exact hm.comp (measurable_raceDraw n)

def markedGapCoefficient {n r : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (u : Fin r → Fin n) (q : Fin r → Fin (Finset.univ \ removed).card)
    (old : Fin n → ℝ) : ℝ :=
  ∏ a, rateKernel (raceGapStart (compactDeletedClocks removed old) (q a)) (w.rate (u a)) /
    (raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) (q a) / n)

def markedNormalizedGaps {n r : ℕ} (w : Weights n) (removed : Finset (Fin n))
    (q : Fin r → Fin (Finset.univ \ removed).card) (old : Fin n → ℝ) : Fin r → ℝ :=
  fun a => raceNormalizedGaps (compactDeletedWeights w removed)
    (compactDeletedClocks removed old) (q a)

lemma measurable_markedGapCoefficient {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin r → Fin n)
    (q : Fin r → Fin (Finset.univ \ removed).card) :
    Measurable (markedGapCoefficient w removed u q) := by
  unfold markedGapCoefficient rateKernel
  apply Finset.measurable_prod
  intro a _
  have hs := (measurable_raceGapStart (q a)).comp (compactDeletedClocks_measurable removed)
  have hW := (measurable_raceGapRate (compactDeletedWeights w removed) (q a)).comp
    (compactDeletedClocks_measurable removed)
  exact (measurable_const.mul ((hs.neg.mul_const (w.rate (u a))).exp)).div
    (hW.div_const n)

lemma measurable_markedNormalizedGaps {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r → Fin (Finset.univ \ removed).card) :
    Measurable (markedNormalizedGaps w removed q) := by
  apply measurable_pi_iff.mpr
  intro a
  exact ((measurable_pi_apply (q a)).comp
    (measurable_raceNormalizedGaps (compactDeletedWeights w removed))).comp
      (compactDeletedClocks_measurable removed)

theorem measurePreserving_markedNormalizedGaps {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card) :
    MeasurePreserving (markedNormalizedGaps w removed q)
      (exponentialRace w) (standardGapLaw r) :=
  (measurePreserving_selectedNormalizedGaps (compactDeletedWeights w removed) q).comp
    (compactDeletedClocks_measurePreserving w removed)

theorem integrable_markedNormalizedGaps_mixed {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card)
    (p : Fin r → ℕ) :
    Integrable (fun old => ∏ a, markedNormalizedGaps w removed q old a ^ p a)
      (exponentialRace w) :=
  (measurePreserving_markedNormalizedGaps w removed q).integrable_comp_of_integrable
    (integrable_mixed_expMeasure_one p)

theorem integral_markedNormalizedGaps_mixed {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card)
    (p : Fin r → ℕ) :
    (∫ old, ∏ a, markedNormalizedGaps w removed q old a ^ p a ∂exponentialRace w) =
      ∏ a, ((p a).factorial : ℝ) := by
  have hp := measurePreserving_markedNormalizedGaps w removed q
  have hm : AEStronglyMeasurable (fun x : Fin r → ℝ => ∏ a, x a ^ p a)
      ((exponentialRace w).map (markedNormalizedGaps w removed q)) := by
    rw [hp.map_eq]
    exact (integrable_mixed_expMeasure_one p).aestronglyMeasurable
  rw [← integral_map hp.measurable.aemeasurable hm, hp.map_eq]
  exact integral_mixed_expMeasure_one p

theorem integral_markedNormalizedGaps_prod {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card) :
    (∫ old, ∏ a, markedNormalizedGaps w removed q old a ∂exponentialRace w) = 1 := by
  simpa using integral_markedNormalizedGaps_mixed w removed q (fun _ => 1)

theorem integral_markedNormalizedGaps_prod_sq {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card) :
    (∫ old, (∏ a, markedNormalizedGaps w removed q old a) ^ 2 ∂exponentialRace w) =
      (2 : ℝ) ^ r := by
  simp_rw [← Finset.prod_pow]
  simpa using integral_markedNormalizedGaps_mixed w removed q (fun _ => 2)

theorem integrable_markedNormalizedGaps_taylorEnvelope {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card) :
    Integrable (fun old => (∑ a, markedNormalizedGaps w removed q old a) *
      ∏ a, markedNormalizedGaps w removed q old a) (exponentialRace w) := by
  exact (measurePreserving_markedNormalizedGaps w removed q).integrable_comp_of_integrable
    integrable_sum_mul_prod_expMeasure_one

theorem integral_markedNormalizedGaps_taylorEnvelope {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin r ↪ Fin (Finset.univ \ removed).card) :
    (∫ old, (∑ a, markedNormalizedGaps w removed q old a) *
      ∏ a, markedNormalizedGaps w removed q old a ∂exponentialRace w) = 2 * (r : ℝ) := by
  have hp := measurePreserving_markedNormalizedGaps w removed q
  have hm : AEStronglyMeasurable (fun x : Fin r → ℝ => (∑ a, x a) * ∏ a, x a)
      ((exponentialRace w).map (markedNormalizedGaps w removed q)) := by
    rw [hp.map_eq]
    exact integrable_sum_mul_prod_expMeasure_one.aestronglyMeasurable
  rw [← integral_map hp.measurable.aemeasurable hm, hp.map_eq]
  simpa only [standardGapLaw, Fintype.card_fin] using
    (integral_sum_mul_prod_expMeasure_one (ι := Fin r))

end Luce
