import Luce.EndpointShellBuffer

noncomputable section
open Filter Set
open scoped Topology BigOperators ENNReal
namespace Luce

def nonnegativeTail (p : ℕ → ℕ → ℝ≥0∞) (n J : ℕ) : ℝ≥0∞ :=
  ∑' j : ℕ, if J ≤ j then p n j else 0

theorem nonnegativeTail_antitone (p : ℕ → ℕ → ℝ≥0∞) (n : ℕ) :
    Antitone (nonnegativeTail p n) := by
  intro J K hJK
  apply ENNReal.tsum_le_tsum
  intro j
  split_ifs <;> simp_all <;> omega

/-- Generic equivalence used only as an internal limit lemma. -/
theorem nonnegativeTail_limit_iff (p : ℕ → ℕ → ℝ≥0∞) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail p n J) atTop) atTop (𝓝 0) ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ J : ℕ,
        ∀ᶠ n : ℕ in atTop, nonnegativeTail p n J < ε := by
  constructor
  · intro h ε hε
    obtain ⟨J, hJ⟩ := (h.eventually (gt_mem_nhds hε)).exists
    exact ⟨J, eventually_lt_of_limsup_lt hJ⟩
  · intro h
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    obtain ⟨J, hJ⟩ := h ε hε
    filter_upwards [eventually_ge_atTop J] with K hK
    apply limsup_le_of_le (by isBoundedDefault)
    exact hJ.mono fun n hn => (nonnegativeTail_antitone p n hK).trans hn.le

theorem buffered_exp_tail_bound (w : WeightArray) (n J : ℕ) :
    nonnegativeTail (bufferedShellExpCost w) n J ≤
      ENNReal.ofReal (Real.exp 1) * shellTailCost w n J +
        ∑' j : ℕ, if J ≤ j then ENNReal.ofReal (Real.exp (1 - Real.sqrt j)) else 0 := by
  rw [shellTailCost, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro j
  by_cases hj : J ≤ j
  · simpa only [if_pos hj] using bufferedShellExpCost_le w n j
  · simp only [if_neg hj, mul_zero, zero_add, le_refl]

theorem EndpointShellAssumption.buffered_exp {w : WeightArray}
    (h : EndpointShellAssumption w) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (bufferedShellExpCost w) n J) atTop)
      atTop (𝓝 0) := by
  apply (nonnegativeTail_limit_iff _).mpr
  intro ε hε
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1)
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := c + 1) (by simp [c]) hε.ne'
  have hδ' : (0 : ℝ≥0∞) < δ := by exact_mod_cast hδ
  obtain ⟨J₁, hJ₁⟩ := (endpointShellAssumption_iff_eventually w).mp h δ hδ'
  have he := ennreal_tendsto_tail_sum summable_buffer_error.tsum_ofReal_ne_top
  obtain ⟨J₂, hJ₂⟩ := eventually_atTop.mp ((ENNReal.tendsto_nhds_zero.mp he) δ hδ')
  refine ⟨max J₁ J₂, ?_⟩
  filter_upwards [hJ₁] with n hn
  apply lt_of_le_of_lt (buffered_exp_tail_bound w n (max J₁ J₂))
  apply lt_of_le_of_lt _ hδε
  calc
    _ ≤ c * (δ : ℝ≥0∞) + δ := add_le_add
      (mul_le_mul' (le_refl c) ((shellTailCost_antitone w n (le_max_left _ _)).trans hn.le))
      (hJ₂ _ (le_max_right _ _))
    _ = (δ : ℝ≥0∞) * (c + 1) := by simp [mul_add, mul_comm]

theorem bufferedShellQCost_le_of_small_tail (w : WeightArray) (n J : ℕ)
    (hsmall : nonnegativeTail (bufferedShellExpCost w) n J ≤ ENNReal.ofReal (1 / 2)) :
    nonnegativeTail (bufferedShellQCost w) n J ≤
      2 * nonnegativeTail (bufferedShellExpCost w) n J := by
  rw [nonnegativeTail, nonnegativeTail, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  by_cases hJj : J ≤ j
  · simp only [if_pos hJj]
    have hcost : bufferedShellExpCost w n j ≤ ENNReal.ofReal (1 / 2) := by
      apply le_trans _ hsmall
      have := ENNReal.le_tsum j (f := fun j => if J ≤ j then bufferedShellExpCost w n j else 0)
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
theorem EndpointShellAssumption.buffered_Q {w : WeightArray}
    (h : EndpointShellAssumption w) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (bufferedShellQCost w) n J) atTop)
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
  apply lt_of_le_of_lt (bufferedShellQCost_le_of_small_tail w n J
    (hn.le.trans (min_le_right _ _)))
  apply lt_of_le_of_lt _ hδε
  simpa only [mul_comm] using mul_le_mul' (le_refl (2 : ℝ≥0∞))
    (hn.le.trans (min_le_left _ _))

/-- Removing the harmless finite cutoff gives the literal manuscript buffer
sum. Empty shells remain excluded, and the order of limits is unchanged. -/
theorem EndpointShellAssumption.buffered_Q_raw {w : WeightArray}
    (h : EndpointShellAssumption w) :
    Tendsto (fun J : ℕ => limsup (fun n : ℕ => ∑' j : ℕ,
      if J ≤ j then
        if hs : (terminalShell n j).Nonempty then
          ENNReal.ofReal (endpointQ (shellFloor w n j hs * ((j : ℝ) - Real.sqrt j)))
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

end Luce
