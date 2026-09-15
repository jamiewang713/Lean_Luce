import Luce.Section4EndpointShells
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

noncomputable section
open Filter Set
open scoped BigOperators Topology ENNReal
namespace Luce

theorem ennreal_tendsto_tail_sum {a : ℕ → ℝ≥0∞} (ha : ∑' j, a j ≠ ⊤) :
    Tendsto (fun J : ℕ => ∑' j : ℕ, if J ≤ j then a j else 0) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_tsum_compl_atTop_zero ha).comp tendsto_finset_range
  have heq (J : ℕ) : (∑' b : {j : ℕ // j ∉ Finset.range J}, a b) =
      ∑' j : ℕ, if J ≤ j then a j else 0 := by
    convert! (tsum_subtype ({j : ℕ | j ∉ Finset.range J}) a) using 1
    apply tsum_congr
    intro j
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Finset.mem_range, not_lt]
  simpa only [Function.comp_def, heq] using h

/-- Membership in a deep logarithmic shell places the label in the
specified terminal fraction. No condition on the weights is used. -/
theorem shell_label_terminal {n j : ℕ} {k : Fin n} (hk : k ∈ terminalShell n j)
    {ε : ℝ} (hε : 0 < ε) (hj : -Real.log ε ≤ (j : ℝ)) :
    (1 - ε) * (n : ℝ) ≤ (k.val : ℝ) + 1 := by
  have hd : (0 : ℝ) < terminalDepth k := by exact_mod_cast terminalDepth_pos k
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt k.isLt
  have he := Real.exp_le_exp.mpr (mem_terminalShell.mp hk).2.1
  rw [Real.exp_log (div_pos hn hd)] at he
  have hm : (terminalDepth k : ℝ) ≤ (n : ℝ) / Real.exp (j : ℝ) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have := (le_div_iff₀ hd).mp he
    nlinarith
  have heps : Real.exp (-(j : ℝ)) ≤ ε := by
    rw [← Real.exp_log hε]
    exact Real.exp_le_exp.mpr (by linarith)
  have hm' : (terminalDepth k : ℝ) ≤ (n : ℝ) * ε := by
    calc
      _ ≤ (n : ℝ) / Real.exp (j : ℝ) := hm
      _ = (n : ℝ) * Real.exp (-(j : ℝ)) := by rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ (n : ℝ) * ε := mul_le_mul_of_nonneg_left heps hn.le
  have hi : (terminalDepth k : ℝ) + ((k.val : ℝ) + 1) = (n : ℝ) + 1 := by
    exact_mod_cast terminalDepth_add_label k
  nlinarith

/-- Compatibility with the old theorem: uniform terminal positivity implies
the exact shell condition. Normalization and profile convergence are not needed. -/
theorem UniformEndpointAssumption.shell {w : WeightArray}
    (h : UniformEndpointAssumption w) : EndpointShellAssumption w := by
  obtain ⟨γ, ε₀, n₀, hγ, hε₀, hrate⟩ := h
  obtain ⟨J₀, hJ₀⟩ := exists_nat_ge (-Real.log ε₀)
  have hs : Summable (fun j : ℕ => Real.exp (-γ * (j : ℝ))) := by
    simpa only [mul_comm] using Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hγ)
  have ht := ennreal_tendsto_tail_sum hs.tsum_ofReal_ne_top
  apply (endpointShellAssumption_iff_eventually w).mpr
  intro ε hε
  obtain ⟨J, hJ, htail⟩ := ((eventually_ge_atTop J₀).and
    (ht.eventually (gt_mem_nhds hε))).exists
  refine ⟨J, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  apply lt_of_le_of_lt _ htail
  apply ENNReal.tsum_le_tsum
  intro j
  by_cases hJj : J ≤ j
  · simp only [if_pos hJj]
    unfold shellCost
    split_ifs with hnonempty
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hf : γ ≤ shellFloor w n j hnonempty := by
        apply le_shellFloor
        intro k hk
        apply hrate n hn k
        apply shell_label_terminal hk hε₀
        exact hJ₀.trans (by exact_mod_cast hJ.trans hJj)
      exact mul_le_mul_of_nonneg_right (neg_le_neg hf) (Nat.cast_nonneg j)
    · exact bot_le
  · simp only [if_neg hJj, le_refl]

end Luce
