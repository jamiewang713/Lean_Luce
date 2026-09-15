import Luce.Section6DeletedOrderMoment
import Luce.Section6InsertionProductBound
import Luce.Section6OrderPartition

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
namespace Luce.Section6

/-- Exact normalized-spacing transfer after deleting labels, on one actual
elimination-order event. The gap law is proved, not a caller premise. -/
theorem deleted_order_normalized_integral {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (sigma : Equiv.Perm (Fin (Finset.univ \ removed).card))
    (H : (Fin (Finset.univ \ removed).card → ℝ) → ℝ) (hH : Measurable H) :
    (∫ old in {old | StrictMono (fun l => compactDeletedClocks removed old (sigma l))},
      H (orderedNormalizedGaps (compactDeletedWeights w removed) sigma (compactDeletedClocks removed old))
        ∂exponentialRace w) =
      (compactDeletedWeights w removed).mass sigma *
        (∫ xi, H xi ∂standardGapLaw (Finset.univ \ removed).card) := by
  let S := {c : Fin (Finset.univ \ removed).card → ℝ | StrictMono (fun l => c (sigma l))}
  have hS : MeasurableSet S := (measurableSet_strictMono_clocks _).preimage
    (measurable_pi_iff.mpr (fun l => measurable_pi_apply (sigma l)))
  have hp := compactDeletedClocks_measurePreserving w removed
  have hr : MeasurePreserving (compactDeletedClocks removed)
      ((exponentialRace w).restrict ((compactDeletedClocks removed) ⁻¹' S))
      ((exponentialRace (compactDeletedWeights w removed)).restrict S) := by
    refine ⟨hp.measurable, ?_⟩
    rw [← Measure.restrict_map hp.measurable hS, hp.map_eq]
  have hm := hH.comp (measurable_orderedNormalizedGaps (compactDeletedWeights w removed) sigma)
  change (∫ old in (compactDeletedClocks removed) ⁻¹' S,
    (H ∘ orderedNormalizedGaps (compactDeletedWeights w removed) sigma) (compactDeletedClocks removed old)
      ∂exponentialRace w) = _
  rw [← integral_map hr.measurable.aemeasurable hm.aestronglyMeasurable, hr.map_eq]
  exact ordered_gap_integral_transfer (compactDeletedWeights w removed) sigma H hH

/-- The full product of actual nonfinal deleted-gap kernels transfers to
one product-space expectation on each elimination-order event. No
independence between insertion factors, or approximation, is assumed. -/
theorem deleted_order_kernel_product_integral {n s : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin s → Fin n)
    (sigma : Equiv.Perm (Fin (Finset.univ \ removed).card))
    (q : Fin s → Fin (Finset.univ \ removed).card) :
    let order := {old | StrictMono (fun l => compactDeletedClocks removed old (sigma l))}
    IntegrableOn (fun old => ∏ e, (deletedGapKernel w removed old (u e) (q e).val).toReal)
      order (exponentialRace w) ∧
    (∫ old in order, ∏ e, (deletedGapKernel w removed old (u e) (q e).val).toReal ∂exponentialRace w) =
      (compactDeletedWeights w removed).mass sigma *
      (∫ xi, ∏ e, exponentialGapMass (w.rate (u e))
        (gapStartFromNormalized (compactDeletedWeights w removed) sigma (q e) xi)
        (xi (q e)/orderedRemainingRate (compactDeletedWeights w removed) sigma (q e))
        ∂standardGapLaw (Finset.univ \ removed).card) := by
  dsimp only
  let S := {old | StrictMono (fun l => compactDeletedClocks removed old (sigma l))}
  let H := fun xi => ∏ e, exponentialGapMass (w.rate (u e))
    (gapStartFromNormalized (compactDeletedWeights w removed) sigma (q e) xi)
    (xi (q e)/orderedRemainingRate (compactDeletedWeights w removed) sigma (q e))
  have hS : MeasurableSet S := (measurableSet_strictMono_clocks _).preimage
    (measurable_pi_iff.mpr (fun l => measurable_pi_apply (deletedClockLabel removed (sigma l))))
  have hm : Measurable H := by
    dsimp [H]
    unfold gapStartFromNormalized exponentialGapMass survivalKernel
    fun_prop
  have he : (fun old => ∏ e, (deletedGapKernel w removed old (u e) (q e).val).toReal) =ᵐ[
      (exponentialRace w).restrict S]
      (fun old => H (orderedNormalizedGaps (compactDeletedWeights w removed) sigma (compactDeletedClocks removed old))) := by
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (exponentialRace_injective_ae w),
      ae_restrict_of_ae (exponentialRace_nonnegative_background w)] with old ho hi hn
    have hc := compactDeletedClocks_injective removed old hi
    have hd : raceDraw (compactDeletedClocks removed old) = sigma := by
      rw [raceDraw_eq _ hc]
      exact (drawPermutation_eq_iff_strictMono _ hc sigma).mpr ho
    apply Finset.prod_congr rfl
    intro e he
    rw [deletedGapKernel_eq_normalizedGapMass w removed old hi hn]
    simp only [raceGapStart, raceNormalizedGaps, raceGapRate, hd]
    rw [gapStartFromNormalized_eq_previous]
  refine ⟨(deleted_kernel_product_integrable w removed u (fun e => (q e).val)).restrict, ?_⟩
  rw [integral_congr_ae he]
  exact deleted_order_normalized_integral w removed sigma H hm

/-- Unconditional product identity, summing every actual elimination order.
The integrability premise of the partition theorem is discharged here. -/
theorem deleted_kernel_product_order_sum {n s : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin s → Fin n)
    (q : Fin s → Fin (Finset.univ \ removed).card) :
    (∫ old, ∏ e, (deletedGapKernel w removed old (u e) (q e).val).toReal ∂exponentialRace w) =
      ∑ sigma : Equiv.Perm (Fin (Finset.univ \ removed).card),
        (compactDeletedWeights w removed).mass sigma *
        (∫ xi, ∏ e, exponentialGapMass (w.rate (u e))
          (gapStartFromNormalized (compactDeletedWeights w removed) sigma (q e) xi)
          (xi (q e)/orderedRemainingRate (compactDeletedWeights w removed) sigma (q e))
          ∂standardGapLaw (Finset.univ \ removed).card) := by
  rw [deleted_order_integral_partition w removed _
    (deleted_kernel_product_integrable w removed u (fun e => (q e).val))]
  exact Finset.sum_congr rfl fun sigma _ =>
    (deleted_order_kernel_product_integral w removed u sigma q).2

end Luce.Section6
