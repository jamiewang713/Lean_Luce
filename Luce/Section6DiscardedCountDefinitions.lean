import Luce.Section6ContractDefinitions

noncomputable section
namespace Luce.Section6

/-- Literal cycles discarded when roots have depth in [A,B] but some
vertex has depth outside [A,B]. Real cutoffs preserve the manuscript domain. -/
def intervalDiscardedCycleCount {n : ℕ} (R : Equiv.Perm (Fin n))
    (side : Corner) (k : ℕ) (A B : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun c : ↥(Section5.cycleOrbits R k) =>
    A ≤ (cornerDistance side (Section5.cycleMaximum R k c) : ℝ) ∧
    (cornerDistance side (Section5.cycleMaximum R k c) : ℝ) ≤ B ∧
    ∃ z ∈ c.val.toFinset,
      ¬ (A ≤ (cornerDistance side z : ℝ) ∧ (cornerDistance side z : ℝ) ≤ B))).card

end Luce.Section6
