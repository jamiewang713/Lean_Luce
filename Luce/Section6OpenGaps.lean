import Luce.Section6SimplexDensityIntegral

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
namespace Luce.Section6

theorem clockBeforeCount_le_size {m : ℕ} (times : Fin m → ℝ) (t : ℝ) :
    clockBeforeCount times t ≤ m := by
  simpa only [clockBeforeCount, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (s := Finset.univ) (p := fun i => times i < t))

/-- T_N, with T_0=0 when no unmarked clocks remain. -/
def terminalGapLower {m : ℕ} (times : Fin m → ℝ) (htimes : Injective times) : ℝ :=
  if hm : 0 < m then arrivalTime times htimes ⟨m-1, by omega⟩ else 0

theorem mem_terminalGap_iff_count {m : ℕ} (times : Fin m → ℝ)
    (htimes : Injective times) (hpos : ∀ i, 0 ≤ times i) (t : ℝ) :
    t ∈ Ioi (terminalGapLower times htimes) ↔ 0 < t ∧ clockBeforeCount times t = m := by
  have hle := clockBeforeCount_le_size times t
  unfold terminalGapLower
  split_ifs with hm
  · have hh := arrivalTime_lt_iff_clockBeforeCount times htimes ⟨m-1, by omega⟩ t
    change arrivalTime times htimes ⟨m-1, _⟩ < t ↔ _
    constructor
    · intro ht
      have hc := hh.mp ht
      exact ⟨(hpos _).trans_lt ht, by dsimp at hc; omega⟩
    · intro ht
      apply hh.mpr
      dsimp
      omega
  · have hm0 : m = 0 := by omega
    simp only [mem_Ioi]
    constructor
    · intro ht
      exact ⟨ht, by omega⟩
    · exact fun ht => ht.1

/-- Every open order-statistic gap, including (0,T_1) and (T_N,infinity).
Indices beyond N describe the empty set. -/
def openOrderGap {m : ℕ} (times : Fin m → ℝ) (htimes : Injective times) (q : ℕ) : Set ℝ :=
  if hq : q < m then
    Ioo (consecutiveGapLower times htimes ⟨q, hq⟩) (arrivalTime times htimes ⟨q, hq⟩)
  else if q = m then Ioi (terminalGapLower times htimes) else ∅

theorem mem_openOrderGap_iff_count {m : ℕ} (times : Fin m → ℝ)
    (htimes : Injective times) (hpos : ∀ i, 0 ≤ times i) (q : ℕ) (t : ℝ)
    (havoid : ∀ i, t ≠ times i) :
    t ∈ openOrderGap times htimes q ↔ 0 < t ∧ clockBeforeCount times t = q := by
  unfold openOrderGap
  split_ifs with hq hqm
  · exact mem_consecutiveGap_iff_count times htimes hpos ⟨q, hq⟩ t havoid
  · subst q
    exact mem_terminalGap_iff_count times htimes hpos t
  · have hle := clockBeforeCount_le_size times t
    simp only [mem_empty_iff_false, false_iff, not_and]
    intro _ he
    omega

theorem measurableSet_openOrderGap {m : ℕ} (times : Fin m → ℝ)
    (htimes : Injective times) (q : ℕ) : MeasurableSet (openOrderGap times htimes q) := by
  unfold openOrderGap
  split_ifs
  · exact measurableSet_Ioo
  · exact measurableSet_Ioi
  · exact MeasurableSet.empty

end Luce.Section6
