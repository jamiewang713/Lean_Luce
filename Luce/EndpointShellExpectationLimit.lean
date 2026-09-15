import Luce.EndpointShellEstimate
import Luce.EndpointShellBufferLimit

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Luce

def shellExpectationCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ i ∈ terminalShell n j,
    (exponentialRace (w n)).real {e | raceRank e i = i.val+1})

theorem shellExpectationCost_le {w : WeightArray} (hnorm : NormalizedWeights w)
    (n j : ℕ) (hj : 4096 ≤ j) :
    shellExpectationCost w n j ≤ ENNReal.ofReal (Real.exp (1-Real.sqrt j)) +
      bufferedShellQCost w n j := by
  classical
  by_cases hb : (terminalShell n j).Nonempty
  · cases n with
    | zero => obtain ⟨i, _⟩ := hb; exact Fin.elim0 i
    | succ n =>
      have h := shell_block_expectation_le hnorm n j hj hb
      rw [block_fixedPoint_expectation_eq] at h
      have hh : 0 < (j : ℝ)-Real.sqrt j := by
        have hj' : (4096 : ℝ) ≤ j := by exact_mod_cast hj
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg j), Real.sqrt_nonneg (j : ℝ)]
      have hq := (endpointQ_pos (mul_pos (shellFloor_pos w (n+1) j hb) hh)).le
      simpa only [shellExpectationCost, bufferedShellQCost,
        dif_pos (show 2 ≤ j by omega), dif_pos hb,
        ENNReal.ofReal_add (Real.exp_pos _).le hq] using ENNReal.ofReal_le_ofReal h
  · simp only [shellExpectationCost, Finset.not_nonempty_iff_eq_empty.mp hb,
      Finset.sum_empty, ENNReal.ofReal_zero, zero_le]

theorem shellExpectationTail_bound {w : WeightArray} (hnorm : NormalizedWeights w)
    (n J : ℕ) (hJ : 4096 ≤ J) :
    nonnegativeTail (shellExpectationCost w) n J ≤
      (∑' j : ℕ, if J ≤ j then ENNReal.ofReal (Real.exp (1-Real.sqrt j)) else 0) +
      nonnegativeTail (bufferedShellQCost w) n J := by
  rw [nonnegativeTail, nonnegativeTail, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro j
  by_cases hj : J ≤ j
  · simpa only [if_pos hj] using shellExpectationCost_le hnorm n j (hJ.trans hj)
  · simp only [if_neg hj, zero_add, le_refl]

/-- Shell expectation tightness is derived from normalization and the raw
shell condition, without any profile or uniform endpoint bound. -/
theorem EndpointShellAssumption.expectation_shells {w : WeightArray}
    (h : EndpointShellAssumption w) (hnorm : NormalizedWeights w) :
    Tendsto (fun J => limsup (fun n => nonnegativeTail (shellExpectationCost w) n J) atTop)
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
  apply lt_of_le_of_lt (shellExpectationTail_bound hnorm n J (le_max_left _ _))
  apply lt_of_le_of_lt _ hδε
  calc
    _ ≤ (δ : ℝ≥0∞) + δ := add_le_add
      (hJ₂ J ((le_max_right J₁ J₂).trans (le_max_right _ _)))
      ((nonnegativeTail_antitone _ n ((le_max_left J₁ J₂).trans (le_max_right _ _))).trans hn.le)
    _ = (δ : ℝ≥0∞) * 2 := by rw [mul_two]

end Luce
