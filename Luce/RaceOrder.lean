import Luce.Model
import Mathlib.Data.Fintype.Card

/-! # The permutation obtained by sorting distinct clocks -/

namespace Luce

/-- The number of clocks strictly earlier than a fixed clock is less than `n`. -/
lemma beforeCount_lt {n : ℕ} (times : Fin n → ℝ) (i : Fin n) :
    (Finset.univ.filter fun j => times j < times i).card < n := by
  classical
  have hs : (Finset.univ.filter fun j => times j < times i) ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hi : i ∈ Finset.univ.filter fun j => times j < times i := by rw [he]; simp
    simpa using hi
  simpa using Finset.card_lt_card hs

/-- Strictly earlier clocks have strictly smaller race ranks. -/
lemma raceRank_strict {n : ℕ} (times : Fin n → ℝ) {i j : Fin n}
    (hij : times i < times j) : raceRank times i < raceRank times j := by
  classical
  have hs : (Finset.univ.filter fun k => times k < times i) ⊂
      (Finset.univ.filter fun k => times k < times j) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.trans hij⟩
    · intro he
      have hi : i ∈ Finset.univ.filter fun k => times k < times i := by
        rw [he]
        simp [hij]
      simpa using hi
  have hc := Finset.card_lt_card hs
  unfold raceRank
  omega

lemma raceRank_injective {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) : Function.Injective (raceRank times) := by
  intro i j he
  apply hinj
  apply le_antisymm
  · by_contra h
    have := raceRank_strict times (lt_of_not_ge h)
    omega
  · by_contra h
    have := raceRank_strict times (lt_of_not_ge h)
    omega

/-- Zero-based rank as a valid position. -/
noncomputable def clockRank {n : ℕ} (times : Fin n → ℝ) (i : Fin n) : Fin n :=
  ⟨(Finset.univ.filter fun j => times j < times i).card, beforeCount_lt times i⟩

lemma clockRank_injective {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) : Function.Injective (clockRank times) := by
  intro i j he
  apply raceRank_injective times hinj
  have hv := congrArg Fin.val he
  simpa only [clockRank, raceRank] using congrArg (1 + ·) hv

/-- The bijective rank map of a family of distinct clocks. -/
noncomputable def rankPermutation {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (clockRank times)
    ⟨clockRank_injective times hinj, Finite.surjective_of_injective (clockRank_injective times hinj)⟩

/-- The draw order is the inverse of the rank permutation. -/
noncomputable def drawPermutation {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) : Equiv.Perm (Fin n) :=
  (rankPermutation times hinj).symm

/-- The `k`th arrival time, with positions represented by `Fin n`. -/
noncomputable def arrivalTime {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) (k : Fin n) : ℝ :=
  times (drawPermutation times hinj k)

lemma clockRank_le_iff {n : ℕ} (times : Fin n → ℝ) (i j : Fin n) :
    clockRank times i ≤ clockRank times j ↔ times i ≤ times j := by
  constructor
  · intro h
    by_contra hn
    have hh := raceRank_strict times (lt_of_not_ge hn)
    change (clockRank times i).val ≤ (clockRank times j).val at h
    simp only [raceRank, clockRank, Fin.val_mk] at *
    omega
  · intro h
    change (Finset.univ.filter fun k => times k < times i).card ≤
      (Finset.univ.filter fun k => times k < times j).card
    apply Finset.card_le_card
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.trans_le h⟩

/-- Equation `eq:survival-indicator`: rank survival equals clock survival. -/
lemma rank_survives_iff {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) (i k : Fin n) :
    k ≤ rankPermutation times hinj i ↔ arrivalTime times hinj k ≤ times i := by
  have hk : clockRank times (drawPermutation times hinj k) = k :=
    (rankPermutation times hinj).apply_symm_apply k
  change k ≤ clockRank times i ↔ times (drawPermutation times hinj k) ≤ times i
  conv_lhs => rw [← hk]
  exact clockRank_le_iff times _ _

/-- Equation `eq:remaining-weight`, evaluated at an arrival time. -/
lemma remaining_eq_clock_survivors {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) (k : Fin n) :
    remaining (drawPermutation times hinj) k =
      Finset.univ.filter fun i => arrivalTime times hinj k ≤ times i := by
  classical
  ext i
  simp only [remaining, Finset.mem_filter, Finset.mem_univ, true_and]
  exact rank_survives_iff times hinj i k

end Luce


