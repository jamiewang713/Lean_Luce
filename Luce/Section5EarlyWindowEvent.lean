import Luce.Section5Insertion
import Luce.Section4EndpointShellEstimate

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce

def earlyGhostSurvivorEvent (n r ell : ℕ) (s : ℝ) : Set (Fin n → ℝ) :=
  {e | (∑ i, clockSurvivalIndicator s i e) ≤ (r : ℝ)+ell}

theorem measurableSet_earlyGhostSurvivorEvent (n r ell : ℕ) (s : ℝ) :
    MeasurableSet (earlyGhostSurvivorEvent n r ell s) :=
  measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_clockSurvivalIndicator s i))
    measurable_const

theorem survival_sum_add_before_le {n : ℕ} (e : Fin n → ℝ) {s t : ℝ} (hts : t ≤ s) :
    (∑ i, clockSurvivalIndicator s i e) + (clockBeforeCount e t : ℝ) ≤ n := by
  classical
  calc
    _ = ∑ i : Fin n, (clockSurvivalIndicator s i e + if e i < t then (1 : ℝ) else 0) := by
      simp only [clockBeforeCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero, Finset.sum_add_distrib]
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      unfold clockSurvivalIndicator
      split_ifs <;> norm_num <;> linarith
    _ = _ := by simp

/-- Any early piece of a target ghost window in a shell forces a low
survivor count at the common cutoff, even at coincident clock times. -/
theorem early_ghost_window_implies_survivor_event {n j : ℕ}
    (e : Fin n → ℝ) (hinj : Function.Injective e) (hpos : ∀ i, 0 ≤ e i)
    (ell : ℕ) (v : Fin n) (hv : v ∈ terminalShell n j)
    (hshell : (terminalShell n j).Nonempty) {s t : ℝ} (hts : t ≤ s)
    (hwindow : GhostWindowByOrder e hinj ell v t) :
    e ∈ earlyGhostSurvivorEvent n (shellMax n j hshell) ell s := by
  have hc := (ghostWindowByOrder_count_bounds e hinj hpos ell v t hwindow).2.1
  have hc' : (v.val : ℝ)+1 ≤ (clockBeforeCount e t : ℝ)+ell := by exact_mod_cast hc
  have hd : terminalDepth v ≤ shellMax n j hshell :=
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  have hd' : (terminalDepth v : ℝ) ≤ shellMax n j hshell := by exact_mod_cast hd
  have hsum : (terminalDepth v : ℝ)+(v.val+1) = (n : ℝ)+1 := by
    exact_mod_cast terminalDepth_add_label v
  have hsurv := survival_sum_add_before_le e hts
  change (∑ i, clockSurvivalIndicator s i e) ≤ (shellMax n j hshell : ℝ)+ell
  linarith

end Luce
