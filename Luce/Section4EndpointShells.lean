import Luce.Section4EndpointShellDefinitions
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

noncomputable section
open Filter Set
open scoped BigOperators Topology ENNReal
namespace Luce

theorem terminalDepth_pos {n : ℕ} (k : Fin n) : 0 < terminalDepth k := by
  unfold terminalDepth
  omega

theorem terminalDepth_le {n : ℕ} (k : Fin n) : terminalDepth k ≤ n := Nat.sub_le _ _

theorem terminalDepth_add_label {n : ℕ} (k : Fin n) :
    terminalDepth k + (k.val + 1) = n + 1 := by
  unfold terminalDepth
  omega

theorem terminalDepth_labelOfDepth {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    terminalDepth (⟨n - m, by omega⟩ : Fin n) = m := by
  change n - (n - m) = m
  omega

theorem terminalDepth_injective (n : ℕ) :
    Function.Injective (terminalDepth : Fin n → ℕ) := by
  intro k l h
  apply Fin.ext
  unfold terminalDepth at h
  omega

theorem mem_terminalShell {n j : ℕ} {k : Fin n} :
    k ∈ terminalShell n j ↔ 1 ≤ j ∧
      (j : ℝ) ≤ Real.log ((n : ℝ) / (terminalDepth k : ℝ)) ∧
      Real.log ((n : ℝ) / (terminalDepth k : ℝ)) < (j : ℝ) + 1 := by
  classical
  simp [terminalShell]

theorem shellFloor_attained (w : WeightArray) (n j : ℕ)
    (h : (terminalShell n j).Nonempty) :
    ∃ k ∈ terminalShell n j, shellFloor w n j h = (w n).rate k := by
  classical
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((terminalShell n j).image (w n).rate) (h.image _))
  exact ⟨k, hk, heq.symm⟩

theorem shellFloor_pos (w : WeightArray) (n j : ℕ)
    (h : (terminalShell n j).Nonempty) : 0 < shellFloor w n j h := by
  obtain ⟨k, _, hk⟩ := shellFloor_attained w n j h
  rw [hk]
  exact (w n).positive k

theorem shellFloor_le_rate (w : WeightArray) {n j : ℕ}
    (h : (terminalShell n j).Nonempty) {k : Fin n} (hk : k ∈ terminalShell n j) :
    shellFloor w n j h ≤ (w n).rate k := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)

theorem le_shellFloor (w : WeightArray) {n j : ℕ}
    (h : (terminalShell n j).Nonempty) {a : ℝ}
    (ha : ∀ k ∈ terminalShell n j, a ≤ (w n).rate k) :
    a ≤ shellFloor w n j h := by
  obtain ⟨k, hk, heq⟩ := shellFloor_attained w n j h
  rw [heq]
  exact ha k hk

/-- A coarse finite bound suffices: no nonempty shell has index greater than n. -/
theorem shell_index_le_row {n j : ℕ} (h : (terminalShell n j).Nonempty) : j ≤ n := by
  obtain ⟨k, hk⟩ := h
  have hd : (0 : ℝ) < terminalDepth k := by exact_mod_cast terminalDepth_pos k
  have hd1 : (1 : ℝ) ≤ terminalDepth k := by exact_mod_cast terminalDepth_pos k
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt k.isLt
  have hdiv : (n : ℝ) / terminalDepth k ≤ n :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn hd)
  have hj := (mem_terminalShell.mp hk).2.1
  have : (j : ℝ) ≤ n := by linarith
  exact_mod_cast this

theorem shellCost_eq_zero_of_row_lt (w : WeightArray) {n j : ℕ} (h : n < j) :
    shellCost w n j = 0 := by
  simp [shellCost, show ¬(terminalShell n j).Nonempty from
    fun hs => (not_le_of_gt h) (shell_index_le_row hs)]

theorem shellCost_le_one (w : WeightArray) (n j : ℕ) : shellCost w n j ≤ 1 := by
  unfold shellCost
  split_ifs with h
  · apply ENNReal.ofReal_le_one.mpr
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (shellFloor_pos w n j h).le) (Nat.cast_nonneg j))
  · exact zero_le_one

/-- This identifies the raw infinite sum with an actual finite row sum. -/
theorem shellTailCost_eq_sum (w : WeightArray) (n J : ℕ) :
    shellTailCost w n J = ∑ j ∈ Finset.range (n + 1),
      if J ≤ j then shellCost w n j else 0 := by
  apply tsum_eq_sum
  intro j hj
  have hn : n < j := by simp only [Finset.mem_range] at hj; omega
  simp [shellCost_eq_zero_of_row_lt w hn]

theorem shellTailCost_ne_top (w : WeightArray) (n J : ℕ) : shellTailCost w n J ≠ ⊤ := by
  rw [shellTailCost_eq_sum]
  apply ne_of_lt
  apply lt_of_le_of_lt (Finset.sum_le_sum (fun j _ => ?_))
    (show (∑ _j ∈ Finset.range (n + 1), (1 : ℝ≥0∞)) < ⊤ by simp)
  split_ifs
  · exact shellCost_le_one w n j
  · exact zero_le_one

theorem shellTailCost_antitone (w : WeightArray) (n : ℕ) : Antitone (shellTailCost w n) := by
  intro J K hJK
  apply ENNReal.tsum_le_tsum
  intro j
  split_ifs <;> simp_all <;> omega

/-- Equivalence, not just a sufficient strengthening. The row threshold is
chosen after the tail cutoff and the requested error. -/
theorem endpointShellAssumption_iff_eventually (w : WeightArray) :
    EndpointShellAssumption w ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ J : ℕ,
        ∀ᶠ n : ℕ in atTop, shellTailCost w n J < ε := by
  constructor
  · intro h ε hε
    obtain ⟨J, hJ⟩ := (h.eventually (gt_mem_nhds hε)).exists
    exact ⟨J, eventually_lt_of_limsup_lt hJ⟩
  · intro h
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact False.elim (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ a from bot_le) ha)
    · intro ε hε
      obtain ⟨δ, hδ, hδε⟩ := exists_between hε
      obtain ⟨J, hJ⟩ := h δ hδ
      filter_upwards [eventually_ge_atTop J] with K hK
      apply lt_of_le_of_lt _ hδε
      apply limsup_le_of_le (by isBoundedDefault)
      exact hJ.mono fun n hn => ((shellTailCost_antitone w n hK).trans hn.le)

end Luce
