import Luce.Section5LateCutoffLimits
import Luce.Section5LateSourceBounds

noncomputable section
open Filter
namespace Luce
attribute [local instance] Classical.propDecidable

/-- The manuscript's two finite truncations: discard high rates globally
and low rates only in the fixed interior. This is a label set, not a new
restriction on WeightArray. -/
def retainedCycleLabels {n : ℕ} (w : Weights n) (M β δ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun u => w.rate u ≤ M ∧ ((u.val : ℝ)+1 ≤ β*n → δ ≤ w.rate u))

def retainedInteriorLabels {n : ℕ} (w : Weights n) (M β δ : ℝ) : Finset (Fin n) :=
  (retainedCycleLabels w M β δ).filter (fun u => (u.val : ℝ)+1 ≤ β*n)

theorem not_mem_retainedCycleLabels {n : ℕ} (w : Weights n) (M β δ : ℝ) (u : Fin n) :
    u ∉ retainedCycleLabels w M β δ ↔
      M < w.rate u ∨ (w.rate u < δ ∧ (u.val : ℝ)+1 ≤ β*n) := by
  simp only [retainedCycleLabels, Finset.mem_filter, Finset.mem_univ, true_and,
    not_and_or, not_le, _root_.not_imp]
  tauto

theorem retainedInteriorLabels_rate {n : ℕ} (w : Weights n) (M β δ : ℝ)
    {u : Fin n} (hu : u ∈ retainedInteriorLabels w M β δ) : δ ≤ w.rate u := by
  have h := Finset.mem_filter.mp hu
  exact (Finset.mem_filter.mp h.1).2.2 h.2

theorem eventually_retained_labels_cover (w : WeightArray) (M δ : ℝ) (J₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ u ∈ retainedCycleLabels (w n) M
        (1 - Real.exp (-(J₀ : ℝ))/2) δ,
      u ∈ retainedInteriorLabels (w n) M (1 - Real.exp (-(J₀ : ℝ))/2) δ ∨
        J₀ ≤ terminalShellNumber u := by
  filter_upwards [eventually_exterior_shellNumber J₀] with n hn
  intro u hu
  by_cases hbulk : (u.val : ℝ)+1 ≤ (1 - Real.exp (-(J₀ : ℝ))/2)*n
  · exact Or.inl (Finset.mem_filter.mpr ⟨hu, hbulk⟩)
  · exact Or.inr (hn u (lt_of_not_ge hbulk))

end Luce
