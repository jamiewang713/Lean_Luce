import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith

/-! # Passing from the endpoint power bound to the left limit

This real analytic helper is used for `eq:tail-tightness` in Section 4 of
`fixed_points.tex`. Its hypotheses are precisely the nonnegativity and local
power bound obtained from the endpoint estimate.
-/

open Filter
open scoped Topology

namespace Luce

theorem tendsto_zero_of_endpoint_power_bound
    (f : ℝ → ℝ) (hf : ∀ α, 0 ≤ f α)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < δ →
      f (1 - ε) ≤ (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4)) :
    Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hsub : Tendsto (fun α : ℝ => 1 - α) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun α : ℝ => 1 - α) (𝓝[<] (1 : ℝ)) (𝓝 (1 - 1 : ℝ)))
  have henv : Tendsto (fun α : ℝ =>
      (2 : ℝ) ^ (1 + γ / 2) * (1 - α) ^ (γ / 4))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (hsub.rpow_const_nhds_zero (by linarith : 0 < γ / 4)).const_mul
        ((2 : ℝ) ^ (1 + γ / 2))
  have hupper : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ),
      f α ≤ (2 : ℝ) ^ (1 + γ / 2) * (1 - α) ^ (γ / 4) := by
    have hnear : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), 1 - δ < α :=
      nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : 1 - δ < 1))
    filter_upwards [self_mem_nhdsWithin, hnear] with α hα hαδ
    have h := hbound (1 - α) (sub_pos.mpr hα) (by linarith)
    simpa only [sub_sub_cancel] using h
  exact squeeze_zero' (Eventually.of_forall hf) hupper henv

end Luce
