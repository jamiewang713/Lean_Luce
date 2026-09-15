import Luce.Section4EndpointSlowLabel
import Luce.Section4EndpointRegularShellLimit
import Luce.Section4EndpointShellPartition
import Luce.Section4EndpointExpectationTightness

/-! Corollary 4.7, `cor:exceptional-shell-refinement`, in
`fixed_points_sampled_profile.tex`. Exceptional terminal depths are represented
by their labels: depth `m` corresponds to `k.val = n-m`. The assumption below
is the literal combined cost, with the original order of limits. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace Luce

def exceptionalTailCharge (w : WeightArray) (E : ∀ n, Finset (Fin n))
    (n J : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ (terminalDepthBlock n J).filter (fun k => k ∈ E n),
    ENNReal.ofReal (slowLabelCharge (w n) k)

/-- Equation `eq:exceptional-shell-condition`. In particular no lower bound
is imposed on exceptional rates, and no profile hypothesis is included. -/
def EndpointExceptionalAssumption (w : WeightArray) (E : ∀ n, Finset (Fin n)) : Prop :=
  Tendsto (fun J : ℕ => limsup (fun n : ℕ =>
    RegularShell.shellTailCost E w n J + exceptionalTailCharge w E n J) atTop)
    atTop (𝓝 (0 : ℝ≥0∞))

theorem EndpointExceptionalAssumption.eventually_small
    {w : WeightArray} {E : ∀ n, Finset (Fin n)}
    (h : EndpointExceptionalAssumption w E) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ᶠ n : ℕ in atTop,
      RegularShell.shellTailCost E w n J + exceptionalTailCharge w E n J < ε := by
  obtain ⟨J, hJ⟩ := (h.eventually (gt_mem_nhds hε)).exists
  exact ⟨J, eventually_lt_of_limsup_lt hJ⟩

theorem EndpointExceptionalAssumption.regular
    {w : WeightArray} {E : ∀ n, Finset (Fin n)}
    (h : EndpointExceptionalAssumption w E) : RegularShell.RegularShellAssumption E w := by
  apply (RegularShell.endpointShellAssumption_iff_eventually E w).mpr
  intro ε hε
  obtain ⟨J, hJ⟩ := h.eventually_small hε
  exact ⟨J, hJ.mono fun n hn => (le_add_of_nonneg_right bot_le).trans_lt hn⟩

theorem terminalDepthBlock_antitone (n : ℕ) : Antitone (terminalDepthBlock n) := by
  classical
  intro J K hJK k hk
  simp only [terminalDepthBlock, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact hk.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (neg_le_neg (Nat.cast_le.mpr hJK))) (Nat.cast_nonneg n))

theorem exceptionalTailCharge_antitone (w : WeightArray) (E : ∀ n, Finset (Fin n))
    (n : ℕ) : Antitone (exceptionalTailCharge w E n) := by
  classical
  intro J K hJK
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (terminalDepthBlock_antitone n hJK)
  · intro k _ _; exact bot_le

theorem regularExpectationTail_eq (w : WeightArray) (E : ∀ n, Finset (Fin n))
    (n J : ℕ) (hJ : 1 ≤ J) :
    nonnegativeTail (RegularShell.shellExpectationCost E w) n J =
      ∑ k ∈ terminalDepthBlock n J, if k ∉ E n then
        ENNReal.ofReal ((exponentialRace (w n)).real {e | raceRank e k = k.val+1}) else 0 := by
  classical
  rw [terminalDepthBlock_sum_eq_shells hJ]
  apply tsum_congr
  intro j
  by_cases hj : J ≤ j
  · simp only [if_pos hj, RegularShell.shellExpectationCost,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)]
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp [RegularShell.terminalShell]
  · simp only [if_neg hj]

theorem shellExpectationTail_le_regular_add_exceptional
    (w : WeightArray) (E : ∀ n, Finset (Fin n)) (n J : ℕ) (hJ : 1 ≤ J) :
    nonnegativeTail (shellExpectationCost w) n J ≤
      nonnegativeTail (RegularShell.shellExpectationCost E w) n J +
        exceptionalTailCharge w E n J := by
  classical
  have he : nonnegativeTail (shellExpectationCost w) n J =
      ∑ k ∈ terminalDepthBlock n J,
        ENNReal.ofReal ((exponentialRace (w n)).real {e | raceRank e k = k.val+1}) := by
    rw [terminalDepthBlock_sum_eq_shells hJ]
    apply tsum_congr
    intro j
    by_cases hj : J ≤ j
    · simp only [if_pos hj, shellExpectationCost,
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)]
    · simp only [if_neg hj]
  rw [he, regularExpectationTail_eq w E n J hJ, exceptionalTailCharge,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ E n
  · simp only [hk, not_true_eq_false, if_false, if_true, zero_add]
    exact ENNReal.ofReal_le_ofReal (race_individual_slow_label_charge (w n) k)
  · simp [hk]

/-- Endpoint shell expectation tightness under precisely the raw combined
assumption. Regular buffering and the individual charge are both proved. -/
theorem EndpointExceptionalAssumption.expectation_shells
    {w : WeightArray} {E : ∀ n, Finset (Fin n)}
    (h : EndpointExceptionalAssumption w E) (hnorm : NormalizedWeights w) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (shellExpectationCost w) n J) atTop)
      atTop (𝓝 0) := by
  apply (nonnegativeTail_limit_iff _).mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := 2) (by norm_num) hε.ne'
  have hδ' : (0 : ℝ≥0∞) < δ := by exact_mod_cast hδ
  obtain ⟨J₁, hJ₁⟩ := (nonnegativeTail_limit_iff _).mp
    (h.regular.expectation_shells E hnorm) δ hδ'
  obtain ⟨J₂, hJ₂⟩ := h.eventually_small hδ'
  let J := max 1 (max J₁ J₂)
  refine ⟨J, ?_⟩
  filter_upwards [hJ₁, hJ₂] with n hn₁ hn₂
  apply lt_of_le_of_lt (shellExpectationTail_le_regular_add_exceptional w E n J (le_max_left _ _))
  apply lt_of_le_of_lt _ hδε
  calc
    _ ≤ (δ : ℝ≥0∞) + δ := add_le_add
      ((nonnegativeTail_antitone _ n ((le_max_left J₁ J₂).trans (le_max_right _ _))).trans hn₁.le)
      ((exceptionalTailCharge_antitone w E n
        ((le_max_right J₁ J₂).trans (le_max_right _ _))).trans
        ((le_add_of_nonneg_left bot_le).trans hn₂.le))
    _ = (δ : ℝ≥0∞) * 2 := by rw [mul_two]

theorem EndpointExceptionalAssumption.expectation_tightness
    {w : WeightArray} {E : ∀ n, Finset (Fin n)}
    (h : EndpointExceptionalAssumption w E) (hnorm : NormalizedWeights w) :
    EndpointExpectationTightness w :=
  endpointExpectationTightness_of_shells (h.expectation_shells hnorm)

/-- The actual expected number of fixed points at depths `m ≤ n exp(-J)`. -/
def terminalDepthExpectation (w : WeightArray) (n J : ℕ) : ℝ :=
  ∫ e, (((terminalDepthBlock n J).filter fun k => raceRank e k = k.val+1).card : ℝ)
    ∂exponentialRace (w n)

theorem terminalDepthExpectation_eq_shells (w : WeightArray) (n J : ℕ) (hJ : 1 ≤ J) :
    ENNReal.ofReal (terminalDepthExpectation w n J) =
      nonnegativeTail (shellExpectationCost w) n J := by
  classical
  rw [terminalDepthExpectation, block_fixedPoint_expectation_eq,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg),
    terminalDepthBlock_sum_eq_shells hJ]
  apply tsum_congr
  intro j
  by_cases hj : J ≤ j
  · simp only [if_pos hj, shellExpectationCost,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)]
  · simp only [if_neg hj]

/-- Equation `eq:shell-tail-tightness`, with extended nonnegative limsups
so an unbounded row sequence cannot be hidden by totalized real limsup. -/
theorem EndpointExceptionalAssumption.terminal_depth_limit
    {w : WeightArray} {E : ∀ n, Finset (Fin n)}
    (h : EndpointExceptionalAssumption w E) (hnorm : NormalizedWeights w) :
    Tendsto (fun J => limsup (fun n => ENNReal.ofReal (terminalDepthExpectation w n J)) atTop)
      atTop (𝓝 0) := by
  apply (h.expectation_shells hnorm).congr'
  filter_upwards [eventually_ge_atTop 1] with J hJ
  simp_rw [terminalDepthExpectation_eq_shells w _ J hJ]

end Luce

