import Luce.Section5GhostCylinder

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem finite_rank_cylinder_reindex {α : Type*} {t n : ℕ} (e : Fin t ≃ α)
    (u j : α → Fin n) :
    {clocks | MarkedRankCylinder (fun a => u (e a)) (fun a => j (e a)) clocks} =
      {clocks | ∀ a, raceRank clocks (u a) = (j a).val+1} := by
  ext clocks
  constructor
  · intro h a
    simpa using h (e.symm a)
  · intro h a
    exact h (e a)

theorem finite_rank_cylinder_domination {α : Type*} [Fintype α] {r n : ℕ}
    (w : Weights n) (M : Fin n → Fin n → ℝ) (C : ℝ)
    (hcyl : ∀ t, t ≤ r → ∀ u j : Fin t → Fin n, Function.Injective u → Function.Injective j →
      (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} ≤ C*∏ a, M (u a) (j a))
    (hcard : Fintype.card α ≤ r) (u j : α → Fin n)
    (hu : Function.Injective u) (hj : Function.Injective j) :
    (exponentialRace w).real {clocks | ∀ a, raceRank clocks (u a) = (j a).val+1} ≤
      C*∏ a, M (u a) (j a) := by
  let e := (Fintype.equivFin α).symm
  have hh := hcyl (Fintype.card α) hcard (fun a => u (e a)) (fun a => j (e a))
    (hu.comp e.injective) (hj.comp e.injective)
  rw [finite_rank_cylinder_reindex e u j, Equiv.prod_comp e (fun a => M (u a) (j a))] at hh
  exact hh

end Luce.Section6
