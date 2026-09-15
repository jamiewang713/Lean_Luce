import Luce.Section6DiscardedCountDefinitions
import Luce.Section4EndpointShells

noncomputable section
namespace Luce.Section6

theorem positive_depth_interval_rounding {m : ℕ} (hm : 0 < m) (A B : ℝ) :
    (A ≤ (m : ℝ) ∧ (m : ℝ) ≤ B) ↔
      ((max 1 ⌈A⌉₊ : ℕ) : ℝ) ≤ m ∧ (m : ℝ) ≤ (⌊B⌋₊ : ℕ) := by
  have hl : max 1 ⌈A⌉₊ ≤ m ↔ A ≤ (m : ℝ) := by
    rw [max_le_iff, Nat.ceil_le]
    simp [show 1 ≤ m from hm]
  have hu := Nat.le_floor_iff' (R := ℝ) (a := B) (Nat.ne_of_gt hm)
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨by exact_mod_cast hl.mpr ha, by exact_mod_cast hu.mpr hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨hl.mp (by exact_mod_cast ha), hu.mp (by exact_mod_cast hb)⟩

/-- Exact cutoff conversion for the literal discarded count, including
negative cutoffs and intervals containing no positive integer depth. -/
theorem interval_discarded_count_rounding {n : ℕ} (R : Equiv.Perm (Fin n))
    (side : Corner) (k : ℕ) (A B : ℝ) :
    intervalDiscardedCycleCount R side k A B =
      intervalDiscardedCycleCount R side k (max 1 ⌈A⌉₊ : ℕ) (⌊B⌋₊ : ℕ) := by
  classical
  have hpos (v : Fin n) : 0 < cornerDistance side v := by
    cases side
    · exact Nat.succ_pos _
    · exact terminalDepth_pos v
  have hi (v : Fin n) := positive_depth_interval_rounding (hpos v) A B
  unfold intervalDiscardedCycleCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c hc
  rw [← and_assoc, ← and_assoc, hi (Section5.cycleMaximum R k c)]
  apply and_congr_right
  intro hroot
  apply exists_congr
  intro z
  exact and_congr_right (fun _ => not_congr (hi z))

theorem interval_discarded_count_eq_zero_of_lt {n : ℕ} (R : Equiv.Perm (Fin n))
    (side : Corner) (k : ℕ) {A B : ℝ} (h : B < A) :
    intervalDiscardedCycleCount R side k A B = 0 := by
  classical
  unfold intervalDiscardedCycleCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨ha, hb, he⟩ := (Finset.mem_filter.mp hc).2
  exact (not_le_of_gt h) (ha.trans hb)

end Luce.Section6
