import Luce.Section65MeanAsymptotic

noncomputable section
open Filter
open scoped Topology
namespace Luce.Section6

theorem MeanApprox65.scale {μ : ℕ → ℝ} {β : ℝ} (h : MeanApprox65 μ β) (hβ : 0 < β) :
    Tendsto (fun n => Real.sqrt (μ n)/Real.sqrt (β*Real.log (n : ℝ))) atTop (𝓝 1) := by
  have hs : Real.sqrt β ≠ 0 := (Real.sqrt_pos.mpr hβ).ne'
  have hh := (Real.continuous_sqrt.continuousAt.tendsto.comp h.ratio).div_const (Real.sqrt β)
  rw [div_self hs] at hh
  apply hh.congr'
  filter_upwards [] with n
  dsimp only [Function.comp_apply]
  rw [Real.sqrt_div' _ (Real.log_natCast_nonneg n),Real.sqrt_mul hβ.le,div_div]
  rw [mul_comm (Real.sqrt (Real.log (n : ℝ))) (Real.sqrt β)]

theorem MeanApprox65.shift {μ : ℕ → ℝ} {β : ℝ} (h : MeanApprox65 μ β) (hβ : 0 < β) :
    Tendsto (fun n => (μ n-β*Real.log (n : ℝ))/Real.sqrt (β*Real.log (n : ℝ))) atTop (𝓝 0) := by
  have hh := h.div_const (Real.sqrt β)
  rw [zero_div] at hh
  apply hh.congr'
  filter_upwards [] with n
  rw [Real.sqrt_mul hβ.le,div_div]
  rw [mul_comm (Real.sqrt (Real.log (n : ℝ))) (Real.sqrt β)]

theorem normalization_affine65 {μ m : ℝ} (hμ : 0 < μ) (hm : 0 < m) (x : ℝ) :
    (x-m)/Real.sqrt m =
      (Real.sqrt μ/Real.sqrt m)*((x-μ)/Real.sqrt μ)+(μ-m)/Real.sqrt m := by
  have hsμ := (Real.sqrt_pos.mpr hμ).ne'
  have hsm := (Real.sqrt_pos.mpr hm).ne'
  field_simp
  ring

end Luce.Section6
