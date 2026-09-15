import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# The two-candidate bound

This formalizes the deterministic counting observation `eq:two-candidate` in
`fixed_points.tex`. At a fixed time, let `survivors` be the set of labels whose
clocks have not rung. Excluding a candidate removes at most one survivor.

The first two statements use the survivor count itself as the index. The last
two use the paper's indices `1, ..., M` and required survivor count `m - 1`.
Taking `candidate m = n - m + 1` gives the paper's terminal-label indexing.

No probabilistic assumptions or injectivity of `candidate` are needed.
-/

namespace Luce

variable {α : Type*} [DecidableEq α]

/-- Among any finite set of natural-number indices, at most two equal the
number of survivors remaining after their candidate is excluded. -/
theorem two_candidate_bound_finset (survivors : Finset α) (candidate : ℕ → α)
    (indices : Finset ℕ) :
    (indices.filter fun m => (survivors.erase (candidate m)).card = m).card ≤ 2 := by
  have hsubset :
      (indices.filter fun m => (survivors.erase (candidate m)).card = m) ⊆
        {survivors.card, survivors.card - 1} := by
    intro m hm
    have hcard := (Finset.mem_filter.mp hm).2.symm
    by_cases hmem : candidate m ∈ survivors
    · have hm' : m = survivors.card - 1 :=
        hcard.trans (Finset.card_erase_of_mem hmem)
      simp [hm']
    · have hm' : m = survivors.card :=
        hcard.trans (congrArg Finset.card (Finset.erase_eq_of_notMem hmem))
      simp [hm']
  exact (Finset.card_le_card hsubset).trans Finset.card_le_two

/-- The two-candidate bound for indices `0, ..., M - 1`. -/
theorem two_candidate_bound (survivors : Finset α) (candidate : ℕ → α) (M : ℕ) :
    ((Finset.range M).filter fun m => (survivors.erase (candidate m)).card = m).card ≤
      2 :=
  two_candidate_bound_finset survivors candidate (Finset.range M)

/-- The paper's counting bound, with indices `1, ..., M` and required count `m - 1`.
The positive lower bound on the indices avoids truncation of natural subtraction. -/
theorem two_candidate_bound_Icc (survivors : Finset α) (candidate : ℕ → α) (M : ℕ) :
    ((Finset.Icc 1 M).filter fun m =>
      (survivors.erase (candidate m)).card = m - 1).card ≤ 2 := by
  have hsubset :
      ((Finset.Icc 1 M).filter fun m =>
        (survivors.erase (candidate m)).card = m - 1) ⊆
          {survivors.card, survivors.card + 1} := by
    intro m hm
    obtain ⟨hindex, hcard⟩ := Finset.mem_filter.mp hm
    have hmpos : 1 ≤ m := (Finset.mem_Icc.mp hindex).1
    by_cases hmem : candidate m ∈ survivors
    · have hspos : 0 < survivors.card :=
        Finset.card_pos.mpr ⟨candidate m, hmem⟩
      rw [Finset.card_erase_of_mem hmem] at hcard
      have hm' : m = survivors.card := by omega
      simp [hm']
    · rw [Finset.erase_eq_of_notMem hmem] at hcard
      have hm' : m = survivors.card + 1 := by omega
      simp [hm']
  exact (Finset.card_le_card hsubset).trans Finset.card_le_two

/-- Equation `eq:two-candidate` as a sum of natural-number indicators. -/
theorem two_candidate_sum_bound (survivors : Finset α) (candidate : ℕ → α) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M,
      if (survivors.erase (candidate m)).card = m - 1 then (1 : ℕ) else 0) ≤ 2 := by
  rw [← Finset.card_filter]
  exact two_candidate_bound_Icc survivors candidate M

end Luce
