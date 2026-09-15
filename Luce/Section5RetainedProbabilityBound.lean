import Luce.Section5MaximumTimeSplit
import Luce.Section5EarlyDeepSum

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- The actual retained maximum-cycle probability sum has the manuscript's
early-shell plus late-source/interior bound. Local cutoff premises are
explicit and are not promoted to assumptions of the frozen main theorem. -/
theorem retained_deep_probability_bound (w : WeightArray) (n J₀ J k : ℕ)
    (S S₀ : Finset (Fin n)) {δ : ℝ} (hδ : 0 < δ) (hJ₀ : 1 ≤ J₀) (hJ : 1 ≤ J)
    (hcut : 1 ≤ δ*((J : ℝ) - Real.sqrt J))
    (hrate : ∀ u ∈ S₀, δ ≤ (w n).rate u)
    (hcover : ∀ u ∈ S, u ∈ S₀ ∨ J₀ ≤ terminalShellNumber u)
    (hfloor : ∀ r ∈ Finset.Icc J₀ n, ∀ hs : (terminalShell n r).Nonempty,
      1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) :
    (∑ v ∈ deepShellLabels n J,
      (exponentialRace (w n)).real (retainedMaximumCycleEvent (k+1) S v)) ≤
    (∑ j ∈ Finset.Icc J n, ∫ old, ∑ v ∈ terminalShell n j, ∑ u : Fin n,
      earlyGhostKernel (w n) (k+2) old u v ((j : ℝ) - Real.sqrt j) *
        markedReturnWeight (ghostEntry (w n) (k+2) old) k v u ∂exponentialRace (w n)) +
      (2*(k+2)+1 : ℕ)^(k+2) *
        (Real.exp (-δ*((J : ℝ) - Real.sqrt J)) +
          ∑ r ∈ Finset.Icc J₀ n, if hs : (terminalShell n r).Nonempty then
            Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0) :=
  (retained_maximum_probability_sum_le_time_split (w n) k S
    (deepShellLabels n J) terminalShellTime).trans
      (add_le_add (early_deep_expectation_le_shell_sum (w n) k J hJ S)
        (late_retained_expectation_bound w n J₀ J k S S₀ hδ hJ₀ hJ hcut hrate hcover hfloor))

end Luce
