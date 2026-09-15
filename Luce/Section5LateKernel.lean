import Luce.Section5EarlyKernel
import Luce.Section5LateCombined

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- The complementary part of the original ghost probability. -/
def lateGhostKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (u v : Fin n) (s : ℝ) : ℝ :=
  ghostEntry w ell old u v - earlyGhostKernel w ell old u v s

theorem lateGhostKernel_eq_entry {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (u v : Fin n) (s : ℝ) :
    lateGhostKernel w ell old u v s = lateGhostEntry w ell old hinj u v s := by
  unfold lateGhostKernel
  rw [ghostEntry_eq_early_add_late w ell old hinj u v s]
  simp only [earlyGhostKernel, dif_pos hinj, add_sub_cancel_left]

theorem lateGhostKernel_nonneg {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (u v : Fin n) (s : ℝ) :
    0 ≤ lateGhostKernel w ell old u v s :=
  sub_nonneg.mpr (earlyGhostKernel_le_ghostEntry w ell old u v s)

theorem integrable_late_return_product {n : ℕ} (w : Weights n) (k : ℕ)
    (v u : Fin n) (s : ℝ) :
    Integrable (fun old => lateGhostKernel w (k+2) old u v s *
      markedReturnWeight (ghostEntry w (k+2) old) k v u) (exponentialRace w) := by
  simp only [lateGhostKernel, sub_mul]
  exact (integrable_marked_return_product w k v u).sub
    (integrable_early_return_product w k v u s)

/-- The combined late bound for the actual canonical race, with the
background hypotheses discharged almost surely, not assumed. -/
theorem late_retained_expectation_bound (w : WeightArray) (n J₀ J k : ℕ)
    (S S₀ : Finset (Fin n)) {δ : ℝ} (hδ : 0 < δ) (hJ₀ : 1 ≤ J₀) (hJ : 1 ≤ J)
    (hcut : 1 ≤ δ*((J : ℝ) - Real.sqrt J))
    (hrate : ∀ u ∈ S₀, δ ≤ (w n).rate u)
    (hcover : ∀ u ∈ S, u ∈ S₀ ∨ J₀ ≤ terminalShellNumber u)
    (hfloor : ∀ r ∈ Finset.Icc J₀ n, ∀ hs : (terminalShell n r).Nonempty,
      1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) :
    (∫ old, ∑ v ∈ deepShellLabels n J, ∑ u ∈ S.filter (fun u => u < v),
      lateGhostKernel (w n) (k+2) old u v (terminalShellTime v) *
        markedReturnWeight (ghostEntry (w n) (k+2) old) k v u
      ∂exponentialRace (w n)) ≤
      (2*(k+2)+1 : ℕ)^(k+2) *
        (Real.exp (-δ*((J : ℝ) - Real.sqrt J)) +
          ∑ r ∈ Finset.Icc J₀ n, if hs : (terminalShell n r).Nonempty then
            Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0) := by
  let B : ℝ := (2*(k+2)+1 : ℕ)^(k+2) *
    (Real.exp (-δ*((J : ℝ) - Real.sqrt J)) +
      ∑ r ∈ Finset.Icc J₀ n, if hs : (terminalShell n r).Nonempty then
        Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0)
  have hbound : ∀ᵐ old ∂exponentialRace (w n),
      (∑ v ∈ deepShellLabels n J, ∑ u ∈ S.filter (fun u => u < v),
        lateGhostKernel (w n) (k+2) old u v (terminalShellTime v) *
          markedReturnWeight (ghostEntry (w n) (k+2) old) k v u) ≤ B := by
    filter_upwards [exponentialRace_injective_ae (w n),
      exponentialRace_nonnegative_background (w n)] with old hinj hnonneg
    simpa only [lateGhostKernel_eq_entry (w n) (k+2) old hinj] using
      late_retained_pairs_bound w n J₀ J (k+2) k old hinj hnonneg S S₀
        hδ hJ₀ hJ hcut hrate hcover hfloor
  calc
    _ ≤ ∫ _old, B ∂exponentialRace (w n) := integral_mono_ae
      (integrable_finsetSum _ (fun v _ => integrable_finsetSum _
        (fun u _ => integrable_late_return_product (w n) k v u _)))
      (integrable_const B) hbound
    _ = _ := by simp [B]

end Luce
