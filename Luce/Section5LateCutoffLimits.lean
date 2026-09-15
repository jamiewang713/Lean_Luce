import Luce.Section5ShellCutoff

noncomputable section
open Filter
open scoped Topology
namespace Luce

theorem shellInteriorCutoff_lt_one (J : ℕ) :
    1 - Real.exp (-(J : ℝ))/2 < 1 := by linarith [Real.exp_pos (-(J : ℝ))]

/-- The spatial interior cutoff is fixed before n. Integer rounding is
absorbed by the factor two already used in the Section 4 shell cover. -/
theorem eventually_exterior_shellNumber (J : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ v : Fin n,
      (1 - Real.exp (-(J : ℝ))/2)*(n : ℝ) < (v.val : ℝ)+1 →
        J ≤ terminalShellNumber v := by
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (2 / Real.exp (-(J : ℝ))))
  filter_upwards [hn] with n hn v hv
  apply Nat.le_floor
  apply spatial_tail_log_lower v _ hv
  exact (div_le_iff₀ (Real.exp_pos _)).mp hn

theorem tendsto_shellBufferTime_atTop :
    Tendsto (fun J : ℕ => (J : ℝ) - Real.sqrt J) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (max 4 (2*b)))] with J hJ
  have h4 : (4 : ℝ) ≤ J := (le_max_left _ _).trans hJ
  have hb : 2*b ≤ (J : ℝ) := (le_max_right _ _).trans hJ
  have hs : 2 ≤ Real.sqrt (J : ℝ) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg J)).mpr
    norm_num
    exact_mod_cast h4
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg J),
    mul_nonneg (Real.sqrt_nonneg (J : ℝ)) (show 0 ≤ Real.sqrt (J : ℝ)-2 by linarith)]

theorem eventually_interior_density_cutoff {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ J : ℕ in atTop, 1 ≤ δ*((J : ℝ) - Real.sqrt J) := by
  filter_upwards [tendsto_shellBufferTime_atTop.eventually (eventually_ge_atTop (1/δ))]
    with J hJ
  have := (div_le_iff₀ hδ).mp hJ
  simpa only [mul_comm] using this

theorem tendsto_interior_late_error {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun J : ℕ => Real.exp (-δ*((J : ℝ) - Real.sqrt J))) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp
    (tendsto_shellBufferTime_atTop.const_mul_atTop_of_neg (neg_neg_of_pos hδ))

end Luce
