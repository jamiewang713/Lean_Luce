import Luce.Section6TerminalGapSurvival

namespace Luce.Section6

/-- Construct a finite reference gap before every gap in a terminal window.
The terminal index itself is allowed; no finite length is assigned to it. -/
theorem terminal_window_reference_gap {n Q h k : ℕ}
    (removed : Finset (Fin n)) (hh : removed.card+Q+1 ≤ h) (hn : h < n)
    (hk : (Finset.univ \ removed).card ≤ k+Q) :
    ∃ q : Fin (Finset.univ \ removed).card, q.val = n-h ∧ q.val ≤ k := by
  classical
  have hc : (Finset.univ \ removed).card = n-removed.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hq : n-h < (Finset.univ \ removed).card := by rw [hc]; omega
  refine ⟨⟨n-h, hq⟩, rfl, ?_⟩
  rw [hc] at hk
  simp only [Fin.val_mk]
  omega

end Luce.Section6
