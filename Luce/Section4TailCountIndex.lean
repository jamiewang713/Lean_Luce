import Luce.Section4TailCount

/-!
# Matching the spatial tail with terminal indices

This is the exact finite counting bridge for the approved tail count. The
paper's label `k.val + 1` lies in `(1 - ε, 1]` precisely when its index counted
back from the last label is at most `ceil (ε * (n + 1))`.
-/

namespace Luce

lemma rankOf_eq_raceRank_for_tail {n : ℕ} (e : Fin n → ℝ) (k : Fin n) :
    rankOf e k = raceRank e k := by
  classical
  simp only [rankOf, raceRank, Finset.filter_erase]
  rw [Finset.erase_eq_of_notMem (by simp)]

lemma spatial_tail_iff_terminal_index {n : ℕ} (k : Fin (n + 1)) (ε : ℝ) :
    (1 - ε) * ((n + 1 : ℕ) : ℝ) < (k.val : ℝ) + 1 ↔
      n + 1 - k.val ≤ ⌈ε * (n + 1)⌉₊ := by
  have hkn : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  rw [show n + 1 - k.val = (n - k.val) + 1 by omega,
    Nat.add_one_le_ceil_iff, Nat.cast_sub hkn]
  simp only [Nat.cast_add, Nat.cast_one]
  constructor <;> intro h <;> nlinarith

/-- The approved spatial count is exactly the terminal-index count, including
the ceiling when `ε * (n + 1)` is not an integer. -/
theorem tailFixedPointCount_eq_terminalFixedPointCount (n : ℕ)
    (e : Fin (n + 1) → ℝ) {ε : ℝ} (_hε : 0 < ε) (hεone : ε < 1) :
    tailFixedPointCount e (1 - ε) =
      terminalFixedPointCount (terminalCandidate n) ⌈ε * (n + 1)⌉₊ e := by
  classical
  have hM : ⌈ε * ((n : ℝ) + 1)⌉₊ ≤ n + 1 := by
    apply Nat.ceil_le.mpr
    simp only [Nat.cast_add, Nat.cast_one]
    exact mul_le_of_le_one_left (by positivity) hεone.le
  unfold tailFixedPointCount terminalFixedPointCount
  symm
  apply Finset.card_bij (fun m _ => terminalCandidate n m)
  · intro m hm
    obtain ⟨hmrange, hmfixed⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmpos, hmM⟩ := Finset.mem_Icc.mp hmrange
    have hmN := hmM.trans hM
    have hval := terminalCandidate_val_add hmpos hmN
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · apply (spatial_tail_iff_terminal_index (terminalCandidate n m) ε).mpr
      have hindex : n + 1 - (terminalCandidate n m).val = m := by omega
      rwa [hindex]
    · simpa only [rankOf_eq_raceRank_for_tail] using hmfixed
  · intro m₁ hm₁ m₂ hm₂ heq
    have hrange₁ := Finset.mem_Icc.mp (Finset.mem_filter.mp hm₁).1
    have hrange₂ := Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1
    have hval₁ := terminalCandidate_val_add hrange₁.1 (hrange₁.2.trans hM)
    have hval₂ := terminalCandidate_val_add hrange₂.1 (hrange₂.2.trans hM)
    have hvaleq := congrArg Fin.val heq
    omega
  · intro k hk
    obtain ⟨_, hkspace, hkfixed⟩ := Finset.mem_filter.mp hk
    have hmpos : 1 ≤ n + 1 - k.val := by omega
    have hmN : n + 1 - k.val ≤ n + 1 := Nat.sub_le _ _
    have hmM := (spatial_tail_iff_terminal_index k ε).mp hkspace
    have hcandidate : terminalCandidate n (n + 1 - k.val) = k := by
      apply Fin.ext
      have hval := terminalCandidate_val_add hmpos hmN
      omega
    refine ⟨n + 1 - k.val, ?_, hcandidate⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hmpos, hmM⟩, ?_⟩
    simpa only [hcandidate, rankOf_eq_raceRank_for_tail] using hkfixed

end Luce
