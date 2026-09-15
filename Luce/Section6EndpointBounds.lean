import Luce.Section6Sampling
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

theorem PowerExpansion.relative_error_tendsto {f : ℝ → ℝ} {c exponent eta : ℝ}
    (h : PowerExpansion f c exponent eta) (heta : 0 < eta) :
    Tendsto (fun s => f s / (c * s ^ exponent) - 1) (𝓝[>] 0) (𝓝 0) := by
  apply h.trans_tendsto
  have ht := (Real.continuous_rpow_const heta.le).tendsto (0 : ℝ)
  have hz : (0 : ℝ) ^ eta = 0 := Real.zero_rpow heta.ne'
  simpa only [hz] using ht.mono_left nhdsWithin_le_nhds

/-- The two-sided power comparison used at the start of Section 6 follows
from the expansion. It is not an independent assumption. -/
theorem PowerExpansion.eventually_comparable {f : ℝ → ℝ} {c exponent eta : ℝ}
    (h : PowerExpansion f c exponent eta) (hc : 0 < c) (heta : 0 < eta) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (c / 2) * s ^ exponent ≤ f s ∧ f s ≤ (3*c/2) * s ^ exponent := by
  have ht := h.relative_error_tendsto heta
  have hb := ht.eventually (Ioo_mem_nhds (by norm_num : -(1/2 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hb, self_mem_nhdsWithin] with s hs hs0
  have hp : 0 < c * s ^ exponent := mul_pos hc (Real.rpow_pos_of_pos hs0 _)
  have hlo : (1/2 : ℝ) ≤ f s / (c * s ^ exponent) := by
    have := hs.1
    linarith
  have hhi : f s / (c * s ^ exponent) ≤ (3/2 : ℝ) := by
    have := hs.2
    linarith
  have hl := (le_div_iff₀ hp).mp hlo
  have hu := (div_le_iff₀ hp).mp hhi
  constructor <;> nlinarith

theorem PowerProfile.right_eventually_comparable {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (c/2) * s ^ beta ≤ f (1-s) ∧ f (1-s) ≤ (3*c/2) * s ^ beta :=
  h.2.2.2.1.2.2.2.eventually_comparable h.2.2.2.1.1 h.2.2.2.1.2.2.1

theorem PowerProfile.left_eventually_comparable {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (c/2) * s ^ (-alpha) ≤ f s ∧ f s ≤ (3*c/2) * s ^ (-alpha) :=
  h.2.2.1.2.2.2.eventually_comparable h.2.2.1.1 h.2.2.1.2.2.1

theorem CriticalProfile.eventually_comparable {f : ℝ → ℝ} {c eta d : ℝ}
    (h : CriticalProfile f c eta d) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (c/2) * s ^ (-1 : ℝ) ≤ f s ∧ f s ≤ (3*c/2) * s ^ (-1 : ℝ) :=
  h.2.2.2.2.1.eventually_comparable h.2.2.1 h.2.2.2.1

end Luce.Section6
