import Luce.Section6RightPopulationError

noncomputable section
namespace Luce.Section6

theorem reciprocal_scaled_rpow {k t : ℝ} (hk : 0 < k) (ht : 0 < t) (a : ℝ) :
    (1/(k*t))^a = k^(-a)*t^(-a) := by
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow, Real.mul_rpow hk.le ht.le]

/-- The decay constant is constructed from the positive exponential rate;
it is not an additional endpoint hypothesis. -/
theorem exponential_le_power {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Real.exp (-(d*t)) ≤ C*t^(-a) := by
  obtain ⟨K, hK, hb⟩ := exists_power_exp_bound ha
  refine ⟨K/d^a, div_pos hK (Real.rpow_pos_of_pos hd _), ?_⟩
  intro t ht
  have hh := hb (d*t) (mul_pos hd ht).le
  rw [Real.mul_rpow hd.le ht.le] at hh
  rw [Real.rpow_neg ht.le]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht a)).mpr
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hd a)).mpr
  nlinarith [hh]

theorem right_perturbation_power_identity {c beta eta t : ℝ}
    (hc : 0 < c) (hb : 0 < beta) (ht : 0 < t) :
    t*(1/(c*t/4))^((beta+eta)/beta) =
      (c/4)^(-((beta+eta)/beta))*t^(-(eta/beta)) := by
  have he : c*t/4 = (c/4)*t := by ring
  rw [he, reciprocal_scaled_rpow (by positivity) ht]
  have hp : t*t^(-((beta+eta)/beta)) = t^(-(eta/beta)) := by
    conv_lhs => lhs; rw [← Real.rpow_one t]
    rw [← Real.rpow_add ht]
    congr 1
    field_simp
    ring
  calc
    _ = (c/4)^(-((beta+eta)/beta))*(t*t^(-((beta+eta)/beta))) := by ring
    _ = _ := by rw [hp]

end Luce.Section6
