import Luce.Section5RetainedLabels
import Luce.Section5VertexCount

noncomputable section
namespace Luce
attribute [local instance] Classical.propDecidable

theorem retained_labels_complement {n : ℕ} (w : Weights n) (M β δ : ℝ) :
    Finset.univ \ retainedCycleLabels w M β δ =
      (Finset.univ.filter (fun u => M < w.rate u)) ∪
        (Finset.univ.filter (fun u => w.rate u < δ ∧ (u.val : ℝ)+1 ≤ β*n)) := by
  ext u
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_mem_retainedCycleLabels,
    Finset.mem_union, Finset.mem_filter]

theorem excluded_short_vertices_le_high_add_interior_low {n : ℕ}
    (w : Weights n) (R : Equiv.Perm (Fin n)) (L : ℕ) (M β δ : ℝ) :
    shortCycleVertexCount R L (Finset.univ \ retainedCycleLabels w M β δ) ≤
      shortCycleVertexCount R L (Finset.univ.filter (fun u => M < w.rate u)) +
      shortCycleVertexCount R L
        (Finset.univ.filter (fun u => w.rate u < δ ∧ (u.val : ℝ)+1 ≤ β*n)) := by
  rw [retained_labels_complement]
  simp only [shortCycleVertexCount, Finset.filter_union]
  exact Finset.card_union_le _ _

end Luce
