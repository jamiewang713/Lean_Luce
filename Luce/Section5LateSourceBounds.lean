import Luce.Section5LatePairBound
import Luce.Section5ShellCutoff

noncomputable section
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

def deepShellLabels (n J : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => J ≤ terminalShellNumber v)

/-- Terminal predecessors are bounded using their own shell cutoff, after
the ordered-pair comparison has been proved for every target. -/
theorem late_terminal_source_bound (w : WeightArray) (n r J ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (hJ : 1 ≤ J) (hs : (terminalShell n r).Nonempty)
    (hfloor : 1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) :
    (∑ v ∈ deepShellLabels n J, ∑ u ∈ (terminalShell n r).filter (fun u => u < v),
      lateGhostEntry (w n) ell old hinj u v (terminalShellTime v) *
        markedReturnWeight (ghostEntry (w n) ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) *
        Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) := by
  apply late_ordered_pairs_bound (w n) ell k old hinj hnonneg
    (deepShellLabels n J) (terminalShell n r) terminalShellTime
    (shellFloor_pos w n r hs) hfloor.le (fun u hu => shellFloor_le_rate w hs hu)
  intro v hv u hu huv
  exact source_shell_time_le_target hu
    (hJ.trans (Finset.mem_filter.mp hv).2) huv

/-- Interior predecessors use their retained low-rate cutoff. There is no
endpoint assumption in this estimate. -/
theorem late_interior_source_bound {n : ℕ} (w : Weights n) (J ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S : Finset (Fin n)) {δ : ℝ} (hδ : 0 < δ) (hJ : 1 ≤ J)
    (hcut : 1 ≤ δ*((J : ℝ) - Real.sqrt J)) (hrate : ∀ u ∈ S, δ ≤ w.rate u) :
    (∑ v ∈ deepShellLabels n J, ∑ u ∈ S.filter (fun u => u < v),
      lateGhostEntry w ell old hinj u v (terminalShellTime v) *
        markedReturnWeight (ghostEntry w ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) * Real.exp (-δ*((J : ℝ) - Real.sqrt J)) := by
  apply late_ordered_pairs_bound w ell k old hinj hnonneg
    (deepShellLabels n J) S terminalShellTime hδ hcut hrate
  intro v hv _ _ _
  exact cutoff_le_terminalShellTime hJ (Finset.mem_filter.mp hv).2

end Luce
