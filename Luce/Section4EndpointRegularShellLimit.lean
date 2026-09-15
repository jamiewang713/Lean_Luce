import Luce.Section4EndpointRegularShells

/-! Square-root buffering and block expectations for the regular subsets. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators Topology ENNReal
namespace Luce.RegularShell
variable (E : ∀ n, Finset (Fin n))
/-- Exponential buffered costs are used only for j≥2, where the cutoff
is positive. Dropping finitely many indices has no effect on the tail limit. -/
def bufferedShellExpCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  if hj : 2 ≤ j then
    if h : (terminalShell E n j).Nonempty then
      ENNReal.ofReal (Real.exp (-shellFloor E w n j h * ((j : ℝ) - Real.sqrt j))) else 0
  else 0

def bufferedShellQCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  if hj : 2 ≤ j then
    if h : (terminalShell E n j).Nonempty then
      ENNReal.ofReal (endpointQ (shellFloor E w n j h * ((j : ℝ) - Real.sqrt j))) else 0
  else 0

theorem bufferedShellExpCost_le (w : WeightArray) (n j : ℕ) :
    bufferedShellExpCost E w n j ≤ ENNReal.ofReal (Real.exp 1) * shellCost E w n j +
      ENNReal.ofReal (Real.exp (1 - Real.sqrt j)) := by
  unfold bufferedShellExpCost
  split_ifs with hj h
  · have hs : 1 ≤ Real.sqrt (j : ℝ) := by
      apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg j)).mpr
      simpa using (show (1 : ℝ) ≤ j by exact_mod_cast (show 1 ≤ j by omega))
    have hb := buffer_exp_bound (shellFloor E w n j h) (Real.sqrt j) hs
    rw [Real.sq_sqrt (Nat.cast_nonneg j)] at hb
    calc
      _ ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-shellFloor E w n j h * (j : ℝ)) +
          Real.exp (1 - Real.sqrt j)) := ENNReal.ofReal_le_ofReal hb
      _ = _ := by rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (Real.exp_pos _).le]; simp only [shellCost, dif_pos h]
  · exact bot_le
  · exact bot_le


theorem buffered_exp_tail_bound (w : WeightArray) (n J : ℕ) :
    nonnegativeTail (bufferedShellExpCost E w) n J ≤
      ENNReal.ofReal (Real.exp 1) * shellTailCost E w n J +
        ∑' j : ℕ, if J ≤ j then ENNReal.ofReal (Real.exp (1 - Real.sqrt j)) else 0 := by
  rw [shellTailCost, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro j
  by_cases hj : J ≤ j
  · simpa only [if_pos hj] using bufferedShellExpCost_le E w n j
  · simp only [if_neg hj, mul_zero, zero_add, le_refl]

theorem RegularShellAssumption.buffered_exp {w : WeightArray}
    (h : RegularShellAssumption E w) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (bufferedShellExpCost E w) n J) atTop)
      atTop (𝓝 0) := by
  apply (nonnegativeTail_limit_iff _).mpr
  intro ε hε
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1)
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := c + 1) (by simp [c]) hε.ne'
  have hδ' : (0 : ℝ≥0∞) < δ := by exact_mod_cast hδ
  obtain ⟨J₁, hJ₁⟩ := (endpointShellAssumption_iff_eventually E w).mp h δ hδ'
  have he := ennreal_tendsto_tail_sum summable_buffer_error.tsum_ofReal_ne_top
  obtain ⟨J₂, hJ₂⟩ := eventually_atTop.mp ((ENNReal.tendsto_nhds_zero.mp he) δ hδ')
  refine ⟨max J₁ J₂, ?_⟩
  filter_upwards [hJ₁] with n hn
  apply lt_of_le_of_lt (buffered_exp_tail_bound E w n (max J₁ J₂))
  apply lt_of_le_of_lt _ hδε
  calc
    _ ≤ c * (δ : ℝ≥0∞) + δ := add_le_add
      (mul_le_mul' (le_refl c) ((shellTailCost_antitone E w n (le_max_left _ _)).trans hn.le))
      (hJ₂ _ (le_max_right _ _))
    _ = (δ : ℝ≥0∞) * (c + 1) := by simp [mul_add, mul_comm]

theorem bufferedShellQCost_le_of_small_tail (w : WeightArray) (n J : ℕ)
    (hsmall : nonnegativeTail (bufferedShellExpCost E w) n J ≤ ENNReal.ofReal (1 / 2)) :
    nonnegativeTail (bufferedShellQCost E w) n J ≤
      2 * nonnegativeTail (bufferedShellExpCost E w) n J := by
  rw [nonnegativeTail, nonnegativeTail, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  by_cases hJj : J ≤ j
  · simp only [if_pos hJj]
    have hcost : bufferedShellExpCost E w n j ≤ ENNReal.ofReal (1 / 2) := by
      apply le_trans _ hsmall
      have := ENNReal.le_tsum j (f := fun j => if J ≤ j then bufferedShellExpCost E w n j else 0)
      simpa only [nonnegativeTail, if_pos hJj] using this
    unfold bufferedShellQCost bufferedShellExpCost at *
    split_ifs with hj hs
    · simp only [dif_pos hj, dif_pos hs] at hcost
      have hr := ENNReal.toReal_mono (by simp : ENNReal.ofReal (1 / 2) ≠ ⊤) hcost
      simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hr
      rw [neg_mul] at hr
      have hb := ENNReal.ofReal_le_ofReal (endpointQ_le_two_exp hr)
      simpa only [neg_mul, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat] using hb
    · simp
    · simp
  · simp only [if_neg hJj, mul_zero, le_refl]

/-- The actual diagonal shell-buffer conclusion, derived from the raw
assumption alone. The cutoff 2 only avoids undefined nonpositive Q arguments. -/
theorem RegularShellAssumption.buffered_Q {w : WeightArray}
    (h : RegularShellAssumption E w) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (bufferedShellQCost E w) n J) atTop)
      atTop (𝓝 0) := by
  apply (nonnegativeTail_limit_iff _).mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := 2) (by norm_num) hε.ne'
  have hδ' : (0 : ℝ≥0∞) < δ := by exact_mod_cast hδ
  have hmin : (0 : ℝ≥0∞) < min (δ : ℝ≥0∞) (ENNReal.ofReal (1 / 2)) :=
    lt_min hδ' (by norm_num)
  obtain ⟨J, hJ⟩ := (nonnegativeTail_limit_iff _).mp h.buffered_exp _ hmin
  refine ⟨J, ?_⟩
  filter_upwards [hJ] with n hn
  apply lt_of_le_of_lt (bufferedShellQCost_le_of_small_tail E w n J
    (hn.le.trans (min_le_right _ _)))
  apply lt_of_le_of_lt _ hδε
  simpa only [mul_comm] using mul_le_mul' (le_refl (2 : ℝ≥0∞))
    (hn.le.trans (min_le_left _ _))

/-- Removing the harmless finite cutoff gives the literal manuscript buffer
sum. Empty shells remain excluded, and the order of limits is unchanged. -/
theorem RegularShellAssumption.buffered_Q_raw {w : WeightArray}
    (h : RegularShellAssumption E w) :
    Tendsto (fun J : ℕ => limsup (fun n : ℕ => ∑' j : ℕ,
      if J ≤ j then
        if hs : (terminalShell E n j).Nonempty then
          ENNReal.ofReal (endpointQ (shellFloor E w n j hs * ((j : ℝ) - Real.sqrt j)))
        else 0
      else 0) atTop) atTop (𝓝 0) := by
  apply h.buffered_Q.congr'
  filter_upwards [eventually_ge_atTop 2] with J hJ
  congr 1
  funext n
  apply tsum_congr
  intro j
  by_cases hj : J ≤ j
  · simp only [nonnegativeTail, bufferedShellQCost, if_pos hj, dif_pos (hJ.trans hj)]
  · simp only [nonnegativeTail, if_neg hj]


def shellExpectationCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ i ∈ terminalShell E n j,
    (exponentialRace (w n)).real {e | raceRank e i = i.val+1})

theorem shellExpectationCost_le {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j : ℕ) (hj : 4096 ≤ j) :
    shellExpectationCost E w n j ≤ ENNReal.ofReal (Real.exp (1-Real.sqrt j)) +
      bufferedShellQCost E w n j := by
  classical
  by_cases hb : (terminalShell E n j).Nonempty
  · cases n with
    | zero => obtain ⟨i, _⟩ := hb; exact Fin.elim0 i
    | succ n =>
      have h := shell_block_expectation_le E hnorm n j hj hb
      rw [block_fixedPoint_expectation_eq] at h
      have hh : 0 < (j : ℝ)-Real.sqrt j := by
        have hj' : (4096 : ℝ) ≤ j := by exact_mod_cast hj
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg j), Real.sqrt_nonneg (j : ℝ)]
      have hq := (endpointQ_pos (mul_pos (shellFloor_pos E w (n+1) j hb) hh)).le
      simpa only [shellExpectationCost, bufferedShellQCost,
        dif_pos (show 2 ≤ j by omega), dif_pos hb,
        ENNReal.ofReal_add (Real.exp_pos _).le hq] using ENNReal.ofReal_le_ofReal h
  · simp only [shellExpectationCost, Finset.not_nonempty_iff_eq_empty.mp hb,
      Finset.sum_empty, ENNReal.ofReal_zero, zero_le]

theorem shellExpectationTail_bound {w : WeightArray} (hnorm : NormalizedWeights w)
    (n J : ℕ) (hJ : 4096 ≤ J) :
    nonnegativeTail (shellExpectationCost E w) n J ≤
      (∑' j : ℕ, if J ≤ j then ENNReal.ofReal (Real.exp (1-Real.sqrt j)) else 0) +
      nonnegativeTail (bufferedShellQCost E w) n J := by
  rw [nonnegativeTail, nonnegativeTail, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro j
  by_cases hj : J ≤ j
  · simpa only [if_pos hj] using shellExpectationCost_le E hnorm n j (hJ.trans hj)
  · simp only [if_neg hj, zero_add, le_refl]

/-- Shell expectation tightness is derived from normalization and the raw
shell condition, without any profile or uniform endpoint bound. -/
theorem RegularShellAssumption.expectation_shells {w : WeightArray}
    (h : RegularShellAssumption E w) (hnorm : NormalizedWeights w) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (shellExpectationCost E w) n J) atTop)
      atTop (𝓝 0) := by
  apply (nonnegativeTail_limit_iff _).mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := 2) (by norm_num) hε.ne'
  have hδ' : (0 : ℝ≥0∞) < δ := by exact_mod_cast hδ
  obtain ⟨J₁, hJ₁⟩ := (nonnegativeTail_limit_iff _).mp h.buffered_Q δ hδ'
  have he := ennreal_tendsto_tail_sum summable_buffer_error.tsum_ofReal_ne_top
  obtain ⟨J₂, hJ₂⟩ := eventually_atTop.mp ((ENNReal.tendsto_nhds_zero.mp he) δ hδ')
  let J := max 4096 (max J₁ J₂)
  refine ⟨J, ?_⟩
  filter_upwards [hJ₁] with n hn
  apply lt_of_le_of_lt (shellExpectationTail_bound E hnorm n J (le_max_left _ _))
  apply lt_of_le_of_lt _ hδε
  calc
    _ ≤ (δ : ℝ≥0∞) + δ := add_le_add
      (hJ₂ J ((le_max_right J₁ J₂).trans (le_max_right _ _)))
      ((nonnegativeTail_antitone _ n ((le_max_left J₁ J₂).trans (le_max_right _ _))).trans hn.le)
    _ = (δ : ℝ≥0∞) * 2 := by rw [mul_two]



end Luce.RegularShell

