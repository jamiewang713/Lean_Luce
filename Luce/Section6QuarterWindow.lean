import Luce.Section6CrossDepthAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter Set
open scoped Topology
namespace Luce.Section6

/-- A fixed lower cutoff makes all shrinking-window and deletion
conditions hold simultaneously. No relation between n and h is needed. -/
theorem quarter_window_cutoff {a u0 D eps : ℝ}
    (ha : 0 < a) (hu0 : 0 < u0) (hD : 0 < D) (heps : 0 < eps) (r : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ h : ℝ, M ≤ h →
      h^(-(1/4 : ℝ)) ≤ u0 ∧ D*h^(-(1/4 : ℝ)) ≤ eps ∧
      8*(r : ℝ) ≤ a*h^(-(1/4 : ℝ))*h := by
  have hu : ∀ᶠ h : ℝ in atTop, h^(-(1/4 : ℝ)) < u0 :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).eventually (Iio_mem_nhds hu0)
  have hd : ∀ᶠ h : ℝ in atTop, h^(-(1/4 : ℝ)) < eps/D :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).eventually (Iio_mem_nhds (div_pos heps hD))
  have hb : ∀ᶠ h : ℝ in atTop, 8*(r : ℝ)/a ≤ h^(3/4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/4)).eventually (eventually_ge_atTop _)
  have hall : ∀ᶠ h : ℝ in atTop, 1 ≤ h ∧ h^(-(1/4 : ℝ)) ≤ u0 ∧
      D*h^(-(1/4 : ℝ)) ≤ eps ∧ 8*(r : ℝ) ≤ a*h^(-(1/4 : ℝ))*h := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hu, hd, hb] with h hh hhu hhd hhb
    have hh0 : 0 < h := zero_lt_one.trans_le hh
    have hid : h^(-(1/4 : ℝ))*h = h^(3/4 : ℝ) := by
      calc
        _ = h^(-(1/4 : ℝ))*h^(1 : ℝ) := by rw [Real.rpow_one]
        _ = h^(-(1/4 : ℝ)+1) := (Real.rpow_add hh0 _ _).symm
        _ = _ := by norm_num
    refine ⟨hh, hhu.le, ?_, ?_⟩
    · have hb' := (lt_div_iff₀ hD).mp hhd
      nlinarith only [hb']
    · have hb' := (div_le_iff₀ ha).mp hhb
      rw [mul_assoc, hid]
      simpa only [mul_comm] using hb'
  obtain ⟨M, hM⟩ := eventually_atTop.mp hall
  exact ⟨max M 1, le_max_right _ _, fun h hh => (hM h ((le_max_left _ _).trans hh)).2⟩

theorem quarter_window_probability_scale {h C : ℝ} (hh : 0 < h) :
    C/((h^(-(1/4 : ℝ)))^2*h) = C*h^(-(1/2 : ℝ)) := by
  have hp : (h^(-(1/4 : ℝ)))^2*h = h^(1/2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = h^(-(1/4 : ℝ)*2)*h^(1 : ℝ) := by norm_num
      _ = h^(-(1/4 : ℝ)*2+1) := (Real.rpow_add hh _ _).symm
      _ = _ := by norm_num
  rw [hp, Real.rpow_neg hh.le, div_eq_mul_inv]

theorem quarter_window_square_root {h : ℝ} (hh : 0 < h) :
    Real.sqrt (h^(-(1/2 : ℝ))) = h^(-(1/4 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hh.le]
  norm_num

end Luce.Section6
