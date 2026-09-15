import Luce.EndpointShellEstimate
import Luce.EndpointShellBufferLimit

/-! Shell geometry after removing an arbitrary set of exceptional labels.
The intermediate regular-shell assumption contains only the raw exponential
costs. It will be derived from Corollary 4.7's combined condition. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators Topology ENNReal
namespace Luce.RegularShell
variable (E : ∀ n, Finset (Fin n))

def terminalShell (n j : ℕ) : Finset (Fin n) := Luce.terminalShell n j \ E n

/-- The finite minimum exists only when the shell is nonempty. -/
def shellFloor (w : WeightArray) (n j : ℕ) (h : (terminalShell E n j).Nonempty) : ℝ :=
  ((terminalShell E n j).image (w n).rate).min' (h.image _)

/-- Empty shells contribute zero, not `exp 0`. -/
def shellCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  if h : (terminalShell E n j).Nonempty then
    ENNReal.ofReal (Real.exp (-shellFloor E w n j h * (j : ℝ))) else 0

/-- The literal sum over all nonempty shells of index at least `J`.
Finite support is proved separately, not presumed in the definition. -/
def shellTailCost (w : WeightArray) (n J : ℕ) : ℝ≥0∞ :=
  ∑' j : ℕ, if J ≤ j then shellCost E w n j else 0

/-- The manuscript's iterated limit, with no uniform-in-row strengthening.
Normalization is deliberately separate. Row zero is empty and irrelevant. -/
def RegularShellAssumption (w : WeightArray) : Prop :=
  Tendsto (fun J : ℕ => limsup (fun n : ℕ => shellTailCost E w n J) atTop)
    atTop (𝓝 (0 : ℝ≥0∞))



theorem shellFloor_attained (w : WeightArray) (n j : ℕ)
    (h : (terminalShell E n j).Nonempty) :
    ∃ k ∈ terminalShell E n j, shellFloor E w n j h = (w n).rate k := by
  classical
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((terminalShell E n j).image (w n).rate) (h.image _))
  exact ⟨k, hk, heq.symm⟩

theorem shellFloor_pos (w : WeightArray) (n j : ℕ)
    (h : (terminalShell E n j).Nonempty) : 0 < shellFloor E w n j h := by
  obtain ⟨k, _, hk⟩ := shellFloor_attained E w n j h
  rw [hk]
  exact (w n).positive k

theorem shellFloor_le_rate (w : WeightArray) {n j : ℕ}
    (h : (terminalShell E n j).Nonempty) {k : Fin n} (hk : k ∈ terminalShell E n j) :
    shellFloor E w n j h ≤ (w n).rate k := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)

theorem le_shellFloor (w : WeightArray) {n j : ℕ}
    (h : (terminalShell E n j).Nonempty) {a : ℝ}
    (ha : ∀ k ∈ terminalShell E n j, a ≤ (w n).rate k) :
    a ≤ shellFloor E w n j h := by
  obtain ⟨k, hk, heq⟩ := shellFloor_attained E w n j h
  rw [heq]
  exact ha k hk

/-- A coarse finite bound suffices: no nonempty shell has index greater than n. -/
theorem shell_index_le_row {n j : ℕ} (h : (terminalShell E n j).Nonempty) : j ≤ n := by
  obtain ⟨k, hk⟩ := h
  have hd : (0 : ℝ) < terminalDepth k := by exact_mod_cast terminalDepth_pos k
  have hd1 : (1 : ℝ) ≤ terminalDepth k := by exact_mod_cast terminalDepth_pos k
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt k.isLt
  have hdiv : (n : ℝ) / terminalDepth k ≤ n :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn hd)
  have hj := (Luce.mem_terminalShell.mp (Finset.mem_sdiff.mp hk).1).2.1
  have : (j : ℝ) ≤ n := by linarith
  exact_mod_cast this

theorem shellCost_eq_zero_of_row_lt (w : WeightArray) {n j : ℕ} (h : n < j) :
    shellCost E w n j = 0 := by
  simp [shellCost, show ¬(terminalShell E n j).Nonempty from
    fun hs => (not_le_of_gt h) (shell_index_le_row E hs)]

theorem shellCost_le_one (w : WeightArray) (n j : ℕ) : shellCost E w n j ≤ 1 := by
  unfold shellCost
  split_ifs with h
  · apply ENNReal.ofReal_le_one.mpr
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (shellFloor_pos E w n j h).le) (Nat.cast_nonneg j))
  · exact zero_le_one

/-- This identifies the raw infinite sum with an actual finite row sum. -/
theorem shellTailCost_eq_sum (w : WeightArray) (n J : ℕ) :
    shellTailCost E w n J = ∑ j ∈ Finset.range (n + 1),
      if J ≤ j then shellCost E w n j else 0 := by
  apply tsum_eq_sum
  intro j hj
  have hn : n < j := by simp only [Finset.mem_range] at hj; omega
  simp [shellCost_eq_zero_of_row_lt E w hn]

theorem shellTailCost_ne_top (w : WeightArray) (n J : ℕ) : shellTailCost E w n J ≠ ⊤ := by
  rw [shellTailCost_eq_sum]
  apply ne_of_lt
  apply lt_of_le_of_lt (Finset.sum_le_sum (fun j _ => ?_))
    (show (∑ _j ∈ Finset.range (n + 1), (1 : ℝ≥0∞)) < ⊤ by simp)
  split_ifs
  · exact shellCost_le_one E w n j
  · exact zero_le_one

theorem shellTailCost_antitone (w : WeightArray) (n : ℕ) : Antitone (shellTailCost E w n) := by
  intro J K hJK
  apply ENNReal.tsum_le_tsum
  intro j
  split_ifs <;> simp_all <;> omega

/-- Equivalence, not just a sufficient strengthening. The row threshold is
chosen after the tail cutoff and the requested error. -/
theorem endpointShellAssumption_iff_eventually (w : WeightArray) :
    RegularShellAssumption E w ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ J : ℕ,
        ∀ᶠ n : ℕ in atTop, shellTailCost E w n J < ε := by
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
      exact hJ.mono fun n hn => ((shellTailCost_antitone E w n hK).trans hn.le)



def shellMax (n j : ℕ) (h : (terminalShell E n j).Nonempty) : ℕ :=
  ((terminalShell E n j).image terminalDepth).max' (h.image _)

theorem shellMax_attained (n j : ℕ) (h : (terminalShell E n j).Nonempty) :
    ∃ k ∈ terminalShell E n j, terminalDepth k = shellMax E n j h := by
  classical
  exact Finset.mem_image.mp (Finset.max'_mem _ (h.image _))

theorem shellMax_pos (n j : ℕ) (h : (terminalShell E n j).Nonempty) :
    0 < shellMax E n j h := by
  obtain ⟨k, _, hk⟩ := shellMax_attained E n j h
  rw [← hk]
  exact terminalDepth_pos k

theorem shellMax_log (n j : ℕ) (h : (terminalShell E n j).Nonempty) :
    (j : ℝ) ≤ Real.log ((n : ℝ) / shellMax E n j h) := by
  obtain ⟨k, hk, heq⟩ := shellMax_attained E n j h
  rw [← heq]
  exact (Luce.mem_terminalShell.mp (Finset.mem_sdiff.mp hk).1).2.1

theorem shell_card_le_max (n j : ℕ) (h : (terminalShell E n j).Nonempty) :
    (terminalShell E n j).card ≤ shellMax E n j h := by
  classical
  have hinj := Finset.card_image_of_injective (terminalShell E n j) (terminalDepth_injective n)
  calc
    _ = ((terminalShell E n j).image terminalDepth).card := hinj.symm
    _ ≤ (Finset.Icc 1 (shellMax E n j h)).card := Finset.card_le_card (by
      intro m hm
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_Icc.mpr ⟨terminalDepth_pos k,
        Finset.le_max' _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)⟩)
    _ = shellMax E n j h := by simp

theorem shellMax_exp_le (n j : ℕ) (h : (terminalShell E n j).Nonempty) :
    (shellMax E n j h : ℝ) * Real.exp (j : ℝ) ≤ n := by
  have hr : (0 : ℝ) < shellMax E n j h := by exact_mod_cast shellMax_pos E n j h
  have hn : (0 : ℝ) < n := by
    obtain ⟨k, _⟩ := h
    exact_mod_cast Nat.zero_lt_of_lt k.isLt
  have he := Real.exp_le_exp.mpr (shellMax_log E n j h)
  rw [Real.exp_log (div_pos hn hr)] at he
  simpa only [mul_comm] using (le_div_iff₀ hr).mp he



theorem shell_survivor_buffer {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j : ℕ) (hs : (terminalShell E n j).Nonempty) :
    (shellMax E n j hs : ℝ) * Real.exp (Real.sqrt j) ≤
      meanSurvivors (w n).rate ((j : ℝ) - Real.sqrt j) := by
  calc
    _ = ((shellMax E n j hs : ℝ) * Real.exp (j : ℝ)) *
        Real.exp (-((j : ℝ) - Real.sqrt j)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (n : ℝ) * Real.exp (-((j : ℝ) - Real.sqrt j)) :=
      mul_le_mul_of_nonneg_right (shellMax_exp_le E n j hs) (Real.exp_pos _).le
    _ ≤ _ := hnorm.meanSurvivors_jensen n _

theorem shell_block_expectation_le {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j : ℕ) (hj : 4096 ≤ j) (hb : (terminalShell E (n+1) j).Nonempty) :
    (∫ e, (((terminalShell E (n+1) j).filter fun i => raceRank e i = i.val+1).card : ℝ)
      ∂exponentialRace (w (n+1))) ≤
      Real.exp (1-Real.sqrt j) +
      endpointQ (shellFloor E w (n+1) j hb * ((j : ℝ)-Real.sqrt j)) := by
  have hh : 64 ≤ Real.sqrt (j : ℝ) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 64) (Nat.cast_nonneg j)).mpr
    exact_mod_cast hj
  have hs : 0 < (j : ℝ) - Real.sqrt j := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg j)]
  have hr : (1 : ℝ) ≤ shellMax E (n+1) j hb := by
    exact_mod_cast shellMax_pos E (n+1) j hb
  have hbuf := shell_survivor_buffer E hnorm (n+1) j hb
  have he := Real.add_one_le_exp (Real.sqrt (j : ℝ))
  have hcut : (shellMax E (n+1) j hb : ℝ) <
      meanSurvivors (w (n+1)).rate ((j : ℝ)-Real.sqrt j)-1 := by
    nlinarith [mul_nonneg (show 0 ≤ (shellMax E (n+1) j hb : ℝ) by linarith)
      (show 0 ≤ Real.exp (Real.sqrt (j : ℝ))-4 by linarith)]
  have hblock := block_endpoint_capacity (w (n+1)) (terminalShell E (n+1) j) hb _ hs hcut
  apply hblock.trans
  apply add_le_add _ (le_refl _)
  apply le_trans (mul_le_mul_of_nonneg_right
    (show ((terminalShell E (n+1) j).card : ℝ) ≤ shellMax E (n+1) j hb by
      exact_mod_cast shell_card_le_max E (n+1) j hb) (Real.exp_pos _).le)
  exact shell_early_envelope hr hh (by linarith)



end Luce.RegularShell

