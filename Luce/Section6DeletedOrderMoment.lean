import Luce.Section6OrderedGapTransfer
import Luce.Section5DeletedGaps
import Luce.Section5FiniteTaylor

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- Transfer the order-wise moment reduction to the actual unmarked clocks
on the original probability space. Deletion imposes no new rate condition. -/
theorem deleted_order_gap_moment_bound {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n)
    (σ : Equiv.Perm (Fin (Finset.univ \ removed).card))
    (q : Fin (Finset.univ \ removed).card) (p : ℕ) :
    let start := fun old => previousOrderedTime (fun l => compactDeletedClocks removed old (σ l)) q
    let len := fun old => compactDeletedClocks removed old (σ q)-start old
    let order := {old | StrictMono (fun l => compactDeletedClocks removed old (σ l))}
    IntegrableOn (fun old => exponentialGapMass (w.rate i) (start old) (len old)^p)
      order (exponentialRace w) ∧
    (∫ old in order, exponentialGapMass (w.rate i) (start old) (len old)^p ∂exponentialRace w) ≤
      (p.factorial : ℝ)*(w.rate i/orderedRemainingRate (compactDeletedWeights w removed) σ q)^p*
      (∫ old in order, Real.exp (-((p : ℝ)*w.rate i*start old)) ∂exponentialRace w) := by
  dsimp only
  let S := {c : Fin (Finset.univ \ removed).card → ℝ | StrictMono (fun l => c (σ l))}
  have hS : MeasurableSet S := (measurableSet_strictMono_clocks _).preimage
    (measurable_pi_iff.mpr (fun l => measurable_pi_apply (σ l)))
  have hp := compactDeletedClocks_measurePreserving w removed
  have hr : MeasurePreserving (compactDeletedClocks removed)
      ((exponentialRace w).restrict ((compactDeletedClocks removed) ⁻¹' S))
      ((exponentialRace (compactDeletedWeights w removed)).restrict S) := by
    refine ⟨hp.measurable, ?_⟩
    rw [← Measure.restrict_map hp.measurable hS, hp.map_eq]
  let H := fun c : Fin (Finset.univ \ removed).card → ℝ =>
    exponentialGapMass (w.rate i) (previousOrderedTime (fun l => c (σ l)) q)
    (c (σ q)-previousOrderedTime (fun l => c (σ l)) q)^p
  let E := fun c : Fin (Finset.univ \ removed).card → ℝ =>
    Real.exp (-((p : ℝ)*w.rate i*previousOrderedTime (fun l => c (σ l)) q))
  have hmH : Measurable H := by
    dsimp [H]
    unfold previousOrderedTime exponentialGapMass survivalKernel
    split_ifs <;> fun_prop
  have hmE : Measurable E := by
    dsimp [E]
    unfold previousOrderedTime
    split_ifs <;> fun_prop
  have ht (F : (Fin (Finset.univ \ removed).card → ℝ) → ℝ) (hF : Measurable F) :
      (∫ old in (compactDeletedClocks removed) ⁻¹' S, F (compactDeletedClocks removed old)
        ∂exponentialRace w) =
      ∫ c in S, F c ∂exponentialRace (compactDeletedWeights w removed) := by
    rw [← integral_map hr.measurable.aemeasurable hF.aestronglyMeasurable, hr.map_eq]
  have hj := ordered_race_gap_moment_bound (compactDeletedWeights w removed) σ q (w.positive i) p
  have hi := hr.integrable_comp_of_integrable hj.1
  refine ⟨hi, ?_⟩
  change (∫ old in (compactDeletedClocks removed) ⁻¹' S, H (compactDeletedClocks removed old)
      ∂exponentialRace w) ≤ _ *
    (∫ old in (compactDeletedClocks removed) ⁻¹' S, E (compactDeletedClocks removed old)
      ∂exponentialRace w)
  rw [ht H hmH, ht E hmE]
  exact hj.2

/-- The same reduction for the literal existing insertion kernel. Background
injectivity and nonnegativity are discharged almost surely, not assumed. -/
theorem deleted_order_kernel_moment_bound {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (i : Fin n)
    (σ : Equiv.Perm (Fin (Finset.univ \ removed).card))
    (q : Fin (Finset.univ \ removed).card) (p : ℕ) :
    let order := {old | StrictMono (fun l => compactDeletedClocks removed old (σ l))}
    IntegrableOn (fun old => (deletedGapKernel w removed old i q.val).toReal^p)
      order (exponentialRace w) ∧
    (∫ old in order, (deletedGapKernel w removed old i q.val).toReal^p ∂exponentialRace w) ≤
      (p.factorial : ℝ)*(w.rate i/orderedRemainingRate (compactDeletedWeights w removed) σ q)^p*
      (∫ old in order, Real.exp (-((p : ℝ)*w.rate i*
        previousOrderedTime (fun l => compactDeletedClocks removed old (σ l)) q))
        ∂exponentialRace w) := by
  dsimp only
  let S := {old : Fin n → ℝ | StrictMono (fun l => compactDeletedClocks removed old (σ l))}
  have hS : MeasurableSet S := (measurableSet_strictMono_clocks _).preimage
    (measurable_pi_iff.mpr (fun l => measurable_pi_apply (deletedClockLabel removed (σ l))))
  have he : (fun old => (deletedGapKernel w removed old i q.val).toReal^p) =ᵐ[
      (exponentialRace w).restrict S]
      (fun old => exponentialGapMass (w.rate i)
        (previousOrderedTime (fun l => compactDeletedClocks removed old (σ l)) q)
        (compactDeletedClocks removed old (σ q)-
          previousOrderedTime (fun l => compactDeletedClocks removed old (σ l)) q)^p) := by
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (exponentialRace_injective_ae w),
      ae_restrict_of_ae (exponentialRace_nonnegative_background w)] with old ho hi hn
    have hc := compactDeletedClocks_injective removed old hi
    have hd : raceDraw (compactDeletedClocks removed old) = σ := by
      rw [raceDraw_eq _ hc]
      exact (drawPermutation_eq_iff_strictMono _ hc σ).mpr ho
    rw [deletedGapKernel_eq_normalizedGapMass w removed old hi hn]
    simp only [raceGapStart, raceNormalizedGaps, raceGapRate, hd]
    rw [← ordered_gap_eq_normalized_div_rate]
  have hj := deleted_order_gap_moment_bound w removed i σ q p
  refine ⟨hj.1.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  exact hj.2

end Luce.Section6
