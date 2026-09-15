import Luce.Section5EarlyWindowEvent
import Luce.Section5MaximumReturnExpectation

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Luce

/-- Literal early part of the existing order-statistic ghost window. -/
def earlyGhostEntry {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i v : Fin n) (s : ℝ) : ℝ :=
  (expMeasure (w.rate i)).real
    ({t | GhostWindowByOrder old hinj ell v t} ∩ Set.Iic s)

/-- Literal complementary late part; the cutoff point belongs to the early part. -/
def lateGhostEntry {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i v : Fin n) (s : ℝ) : ℝ :=
  (expMeasure (w.rate i)).real
    ({t | GhostWindowByOrder old hinj ell v t} \ Set.Iic s)

theorem ghostEntry_eq_early_add_late {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i v : Fin n) (s : ℝ) :
    ghostEntry w ell old i v =
      earlyGhostEntry w ell old hinj i v s + lateGhostEntry w ell old hinj i v s := by
  letI := isProbabilityMeasure_expMeasure (w.positive i)
  simpa only [earlyGhostEntry, lateGhostEntry, ghostEntry, ghostOrderKernel,
    dif_pos hinj, Measure.real] using
    (measureReal_inter_add_sdiff (μ := expMeasure (w.rate i))
      (s := {t | GhostWindowByOrder old hinj ell v t}) measurableSet_Iic).symm

theorem earlyGhostEntry_le {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (i v : Fin n) (s : ℝ) :
    earlyGhostEntry w ell old hinj i v s ≤ ghostEntry w ell old i v := by
  letI := isProbabilityMeasure_expMeasure (w.positive i)
  simpa only [earlyGhostEntry, ghostEntry, ghostOrderKernel, dif_pos hinj, Measure.real]
    using (measureReal_mono (μ := expMeasure (w.rate i))
      (Set.inter_subset_left :
        {t | GhostWindowByOrder old hinj ell v t} ∩ Set.Iic s ⊆ _))

theorem earlyGhostEntry_eq_zero_off_event {n j : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (i v : Fin n) (hv : v ∈ terminalShell n j)
    (hshell : (terminalShell n j).Nonempty) (s : ℝ)
    (hnot : old ∉ earlyGhostSurvivorEvent n (shellMax n j hshell) ell s) :
    earlyGhostEntry w ell old hinj i v s = 0 := by
  have hempty : {t | GhostWindowByOrder old hinj ell v t} ∩ Set.Iic s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact hnot (early_ghost_window_implies_survivor_event old hinj hnonneg ell v hv
      hshell ht.2 ht.1)
  simp [earlyGhostEntry, hempty]

/-- Pointwise domination by the full return contribution on the early
survivor event. This is a bound, not a redefinition of the actual edge. -/
theorem early_ghost_return_le_event_indicator {n j : ℕ} (w : Weights n) (k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (hshell : (terminalShell n j).Nonempty) (s : ℝ) :
    (∑ v ∈ terminalShell n j, ∑ u : Fin n,
      earlyGhostEntry w (k+2) old hinj u v s *
        markedReturnWeight (ghostEntry w (k+2) old) k v u) ≤
    (earlyGhostSurvivorEvent n (shellMax n j hshell) (k+2) s).indicator
      (fun old => ∑ v ∈ terminalShell n j, ∑ u : Fin n,
        ghostEntry w (k+2) old u v *
          markedReturnWeight (ghostEntry w (k+2) old) k v u) old := by
  classical
  by_cases hmem : old ∈ earlyGhostSurvivorEvent n (shellMax n j hshell) (k+2) s
  · rw [Set.indicator_of_mem hmem]
    apply Finset.sum_le_sum
    intro v _
    apply Finset.sum_le_sum
    intro u _
    exact mul_le_mul_of_nonneg_right (earlyGhostEntry_le w (k+2) old hinj u v s)
      (markedReturnWeight_nonneg _ (fun u v => (ghostEntry_mem_Icc w (k+2) old u v).1) k v u)
  · rw [Set.indicator_of_notMem hmem]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.sum_eq_zero
    intro u _
    rw [earlyGhostEntry_eq_zero_off_event w (k+2) old hinj hnonneg u v hv hshell s hmem,
      zero_mul]

end Luce
