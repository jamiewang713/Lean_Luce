import Luce.Section6LeftInsertionReduction
import Luce.Section6RightInsertionReduction
import Luce.Section5MarkedSort

noncomputable section
namespace Luce.Section6

/-- Left full rank h corresponds to undeleted gap h-1. Bounded gap shifts
give comparable positive actual depths and the existing floor's rank cutoff. -/
theorem shifted_left_gap_bounds {r h q : ℕ} (hh : 8*r+8 ≤ h)
    (hshift : Nat.dist q (h-1) ≤ r+1) :
    4*r+4 ≤ q ∧ q ≤ 2*h ∧ h ≤ 2*q := by
  unfold Nat.dist at hshift
  omega

/-- In the left endpoint range, bounded deletions and shifts cannot reach
the terminal gap. This supplies the Fin index used by the moment theorem. -/
theorem shifted_left_nonterminal {n d r h q : ℕ} (hd : d ≤ r)
    (hh : 8*r+8 ≤ h) (hhn : 2*h ≤ n)
    (hshift : Nat.dist q (h-1) ≤ r+1) : q < n-d := by
  unfold Nat.dist at hshift
  omega

/-- At right depth h, the full-rank gap is n-h. After d deletions the
survivor count is n-d-q. In this range the terminal gap is impossible. -/
theorem shifted_right_survivor_bounds {n d r h q : ℕ}
    (hd : d ≤ r) (hhn : h ≤ n) (hh : 8*r+8 ≤ h)
    (hshift : Nat.dist q (n-h) ≤ r+1) :
    q < n-d ∧ h ≤ 2*(n-d-q) ∧ n-d-q ≤ 2*h := by
  unfold Nat.dist at hshift
  omega

/-- The exact sorted demanded gaps meet the bounded-shift condition.
The one-based manuscript rank is one more than the target Fin value. -/
theorem sorted_demanded_gap_shift {n r : ℕ} (j : Fin r → Fin n)
    (hj : Function.Injective j) (a : Fin r) :
    Nat.dist (sortedMarkedGapIndex j a) (j (Tuple.sort j a)).val ≤ r+1 := by
  have he := sortedMarkedGapIndex_add j hj a
  have ha := a.isLt
  unfold Nat.dist
  omega

end Luce.Section6
