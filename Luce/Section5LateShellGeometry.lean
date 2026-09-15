import Luce.EndpointShellBufferLimit
import Luce.EndpointShellGeometry

noncomputable section
open Filter
open scoped Topology ENNReal
namespace Luce

theorem shell_buffer_time_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x - Real.sqrt x ≤ y - Real.sqrt y := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hsx : 1 ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hx0).mpr
    simpa using hx
  have hss := Real.sqrt_le_sqrt hxy
  nlinarith [Real.sq_sqrt hx0, Real.sq_sqrt hy0,
    mul_nonneg (sub_nonneg.mpr hss)
      (show 0 ≤ Real.sqrt y + Real.sqrt x - 1 by linarith)]

/-- Keeping the marked predecessor below the root is essential for this
comparison; the logarithmic shells themselves need no regularity. -/
theorem predecessor_shell_index_le {n r j : ℕ} {u v : Fin n}
    (hu : u ∈ terminalShell n r) (hv : v ∈ terminalShell n j) (huv : u < v) : r ≤ j := by
  have hd : terminalDepth v ≤ terminalDepth u := by
    unfold terminalDepth
    have := Fin.lt_def.mp huv
    omega
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt u.isLt
  have hdu : (0 : ℝ) < terminalDepth u := by exact_mod_cast terminalDepth_pos u
  have hdv : (0 : ℝ) < terminalDepth v := by exact_mod_cast terminalDepth_pos v
  have hlog : Real.log ((n : ℝ) / terminalDepth u) ≤
      Real.log ((n : ℝ) / terminalDepth v) :=
    Real.log_le_log (div_pos hn hdu)
      (div_le_div_of_nonneg_left hn.le hdv (by exact_mod_cast hd))
  have hr := (mem_terminalShell.mp hu).2.1
  have hj := (mem_terminalShell.mp hv).2.2
  have : (r : ℝ) < (j : ℝ) + 1 := by linarith
  have : r < j + 1 := by exact_mod_cast this
  omega

theorem predecessor_shell_buffer_le {n r j : ℕ} {u v : Fin n}
    (hu : u ∈ terminalShell n r) (hv : v ∈ terminalShell n j) (huv : u < v) :
    (r : ℝ) - Real.sqrt r ≤ (j : ℝ) - Real.sqrt j :=
  shell_buffer_time_mono (by exact_mod_cast (mem_terminalShell.mp hu).1)
    (by exact_mod_cast predecessor_shell_index_le hu hv huv)

/-- The late-density monotonicity threshold is proved from the raw shell
assumption. It is eventual in n, with J chosen first, not a uniform rate floor. -/
theorem EndpointShellAssumption.eventually_buffered_floor_gt_one {w : WeightArray}
    (h : EndpointShellAssumption w) :
    ∃ J : ℕ, 2 ≤ J ∧ ∀ᶠ n in atTop, ∀ r : ℕ, J ≤ r →
      ∀ hs : (terminalShell n r).Nonempty,
        1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r) := by
  obtain ⟨J₀, hJ₀⟩ := (nonnegativeTail_limit_iff _).mp h.buffered_exp
    (ENNReal.ofReal (Real.exp (-1))) (by positivity)
  refine ⟨max J₀ 2, le_max_right _ _, ?_⟩
  filter_upwards [hJ₀] with n hn
  intro r hr hs
  have hr2 : 2 ≤ r := (le_max_right _ _).trans hr
  have hrJ : J₀ ≤ r := (le_max_left _ _).trans hr
  have hcost : bufferedShellExpCost w n r < ENNReal.ofReal (Real.exp (-1)) := by
    apply lt_of_le_of_lt _ hn
    simpa only [nonnegativeTail, if_pos hrJ] using
      (ENNReal.le_tsum r (f := fun j => if J₀ ≤ j then bufferedShellExpCost w n j else 0))
  simp only [bufferedShellExpCost, dif_pos hr2, dif_pos hs] at hcost
  have hexp : Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) <
      Real.exp (-1) := (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mp hcost
  have := Real.exp_lt_exp.mp hexp
  nlinarith

end Luce
