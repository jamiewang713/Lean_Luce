import Luce.Section5GhostTimeSplit
import Luce.Section5EarlyReturn

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- The actual early window probability, with the same null-background
extension as the original ghost kernel. -/
def earlyGhostKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i v : Fin n) (s : ℝ) : ℝ :=
  if h : Function.Injective old then earlyGhostEntry w ell old h i v s else 0

theorem earlyGhostKernel_ae_eq_count {n : ℕ} (w : Weights n) (ell : ℕ)
    (i v : Fin n) (s : ℝ) :
    (fun old => earlyGhostKernel w ell old i v s) =ᵐ[exponentialRace w]
      (fun old => (expMeasure (w.rate i)).real
        {t | GhostCountWindow ell old v t ∧ t ≤ s}) := by
  filter_upwards [exponentialRace_injective_ae w,
    exponentialRace_nonnegative_background w] with old hinj hnonneg
  simp only [earlyGhostKernel, dif_pos hinj, earlyGhostEntry, Measure.real]
  congr 1
  apply measure_congr
  filter_upwards [exponential_avoids_background old (w.rate i)] with t ht
  exact propext (and_congr
    (ghostWindowByOrder_iff_count old hinj hnonneg ell v t ht) Iff.rfl)

theorem aestronglyMeasurable_earlyGhostKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (i v : Fin n) (s : ℝ) :
    AEStronglyMeasurable (fun old => earlyGhostKernel w ell old i v s)
      (exponentialRace w) := by
  letI := isProbabilityMeasure_expMeasure (w.positive i)
  have hm : Measurable (fun old => expMeasure (w.rate i)
      {t | GhostCountWindow ell old v t ∧ t ≤ s}) := by
    apply measurable_measure_prodMk_left (s :=
      {c : (Fin n → ℝ) × ℝ | GhostCountWindow ell c.1 v c.2 ∧ c.2 ≤ s})
    exact (measurableSet_ghostCountWindow ell _ v _
      (fun i => (measurable_pi_apply i).comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  exact hm.ennreal_toReal.aestronglyMeasurable.congr
    (earlyGhostKernel_ae_eq_count w ell i v s).symm

theorem earlyGhostKernel_nonneg {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i v : Fin n) (s : ℝ) :
    0 ≤ earlyGhostKernel w ell old i v s := by
  unfold earlyGhostKernel earlyGhostEntry
  split_ifs <;> positivity

theorem earlyGhostKernel_le_ghostEntry {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (i v : Fin n) (s : ℝ) :
    earlyGhostKernel w ell old i v s ≤ ghostEntry w ell old i v := by
  unfold earlyGhostKernel
  split_ifs with h
  · exact earlyGhostEntry_le w ell old h i v s
  · exact (ghostEntry_mem_Icc w ell old i v).1

theorem integrable_early_return_product {n : ℕ} (w : Weights n) (k : ℕ)
    (v u : Fin n) (s : ℝ) :
    Integrable (fun old => earlyGhostKernel w (k+2) old u v s *
      markedReturnWeight (ghostEntry w (k+2) old) k v u) (exponentialRace w) := by
  have hm : AEStronglyMeasurable
      (fun old => markedReturnWeight (ghostEntry w (k+2) old) k v u)
      (exponentialRace w) := by
    unfold markedReturnWeight forwardPathWeight
    exact Finset.aestronglyMeasurable_fun_sum _ (fun t _ =>
      Finset.aestronglyMeasurable_fun_prod _ (fun a _ =>
        (aemeasurable_ghostOrderKernel w (k+2) _ _).ennreal_toReal.aestronglyMeasurable))
  apply (integrable_marked_return_product w k v u).mono'
    ((aestronglyMeasurable_earlyGhostKernel w (k+2) u v s).mul hm)
  filter_upwards [] with old
  have hp := markedReturnWeight_nonneg (ghostEntry w (k+2) old)
    (fun i j => (ghostEntry_mem_Icc w (k+2) old i j).1) k v u
  change ‖earlyGhostKernel w (k+2) old u v s *
    markedReturnWeight (ghostEntry w (k+2) old) k v u‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (earlyGhostKernel_nonneg w (k+2) old u v s) hp)]
  exact mul_le_mul_of_nonneg_right (earlyGhostKernel_le_ghostEntry w (k+2) old u v s) hp

/-- Integrated early contribution of the actual split ghost edge. -/
theorem early_ghost_return_expectation {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j k : ℕ) (hshell : (terminalShell n j).Nonempty)
    (hj : (64 + 2 * (k + 2 + 1)) ^ 2 ≤ j) :
    (∫ old, ∑ v ∈ terminalShell n j, ∑ u : Fin n,
      earlyGhostKernel (w n) (k+2) old u v ((j : ℝ) - Real.sqrt j) *
        markedReturnWeight (ghostEntry (w n) (k+2) old) k v u
      ∂exponentialRace (w n)) ≤
      (2*(k+2)+1 : ℕ)^(k+1) * Real.exp (1 - Real.sqrt j) := by
  apply le_trans _ (early_shell_return_expectation hnorm n j k hshell hj)
  rw [← integral_indicator (measurableSet_earlyGhostSurvivorEvent _ _ _ _)]
  apply integral_mono_ae
    (integrable_finsetSum _ (fun v _ => integrable_finsetSum _
      (fun u _ => integrable_early_return_product (w n) k v u _)))
    ((integrable_finsetSum _ (fun v _ => integrable_finsetSum _
      (fun u _ => integrable_marked_return_product (w n) k v u))).indicator
        (measurableSet_earlyGhostSurvivorEvent _ _ _ _))
  filter_upwards [exponentialRace_injective_ae (w n),
    exponentialRace_nonnegative_background (w n)] with old hinj hnonneg
  simpa only [earlyGhostKernel, dif_pos hinj] using
    early_ghost_return_le_event_indicator (w n) k old hinj hnonneg hshell
      ((j : ℝ) - Real.sqrt j)

end Luce
