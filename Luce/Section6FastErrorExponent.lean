import Luce.Section6EndpointBounds

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

/-- A smaller error exponent follows from the original relative expansion.
This lets the fast-endpoint proof choose an integrable power envelope
without adding a stronger expansion hypothesis. -/
theorem PowerExpansion.mono_error_exponent {f : ℝ → ℝ} {c p eta eta' : ℝ}
    (h : PowerExpansion f c p eta) (he : eta' ≤ eta) : PowerExpansion f c p eta' := by
  apply h.trans
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with s hs hs1
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hs eta),
    abs_of_pos (Real.rpow_pos_of_pos hs eta'), one_mul] using
    Real.rpow_le_rpow_of_exponent_ge hs hs1.le he

theorem PowerExpansion.exists_fast_error_exponent {f : ℝ → ℝ} {c alpha eta : ℝ}
    (h : PowerExpansion f c (-alpha) eta) (ha : 1 < alpha) (he : 0 < eta) :
    ∃ eta' : ℝ, 0 < eta' ∧ eta' < eta ∧ eta' < alpha-1 ∧
      PowerExpansion f c (-alpha) eta' := by
  let eta' := min (eta/2) ((alpha-1)/2)
  have hp : 0 < eta' := lt_min (half_pos he) (half_pos (sub_pos.mpr ha))
  have hle : eta' < eta := (min_le_left _ _).trans_lt (by linarith)
  have hla : eta' < alpha-1 := (min_le_right _ _).trans_lt (by linarith)
  exact ⟨eta', hp, hle, hla, h.mono_error_exponent hle.le⟩

end Luce.Section6
