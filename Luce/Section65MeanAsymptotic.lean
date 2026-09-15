import Luce.Section65RapidError
import Mathlib.Analysis.Real.Sqrt

noncomputable section
open Filter
open scoped Topology
namespace Luce.Section6

def MeanApprox65 (μ : ℕ → ℝ) (β : ℝ) : Prop :=
  Tendsto (fun n => (μ n-β*Real.log (n : ℝ))/Real.sqrt (Real.log (n : ℝ))) atTop (𝓝 0)

theorem MeanApprox65.ratio {μ : ℕ → ℝ} {β : ℝ} (h : MeanApprox65 μ β) :
    Tendsto (fun n => μ n/Real.log (n : ℝ)) atTop (𝓝 β) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hlog)
  have hh := (h.mul hi).add_const β
  simp only [mul_zero, zero_add] at hh
  apply hh.congr'
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  have hs : Real.sqrt (Real.log (n : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hsq := Real.sq_sqrt hn.le
  simp only [Function.comp_apply]
  rw [← div_eq_mul_inv, div_div, ← pow_two, hsq]
  field_simp
  ring

theorem logGrowth65_of_ratio {μ : ℕ → ℝ} {β : ℝ}
    (h : Tendsto (fun n => μ n/Real.log (n : ℝ)) atTop (𝓝 β)) : LogGrowth65 μ := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have habs := h.abs
  refine ⟨|β|+1,by positivity,1,?_⟩
  filter_upwards [habs.eventually (gt_mem_nhds (show |β| < |β|+1 by linarith)),
    hlog.eventually_gt_atTop 0] with n hn hl
  rw [abs_div, abs_of_pos hl] at hn
  have hb := (div_lt_iff₀ hl).mp hn
  dsimp [logWeight65]
  rw [pow_one]
  nlinarith [abs_nonneg β]

theorem MeanApprox65.growth {μ : ℕ → ℝ} {β : ℝ} (h : MeanApprox65 μ β) :
    LogGrowth65 μ := logGrowth65_of_ratio h.ratio

theorem MeanApprox65.diverges {μ : ℕ → ℝ} {β : ℝ} (h : MeanApprox65 μ β) (hβ : 0 < β) :
    Tendsto μ atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := h.ratio
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hh.eventually (lt_mem_nhds (show β/2 < β by linarith)),
    hlog.eventually_ge_atTop (2*b/β), hlog.eventually_gt_atTop 0] with n hn hb hl
  have hmul := (lt_div_iff₀ hl).mp hn
  have hmul' := (div_le_iff₀ hβ).mp hb
  nlinarith

end Luce.Section6
