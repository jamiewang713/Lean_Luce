import Luce.Section6LeftArrivalAsymptotic

noncomputable section
namespace Luce.Section6

theorem deletedG_le_populationG {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    deletedG w removed t ≤ populationG w t := by
  unfold deletedG populationG
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
  intro i _ _
  exact sub_nonneg.mpr (survivalKernel_le_one ht (w.positive i).le)

/-- A coarse arrival envelope sufficient for exponential lower tails of
the gap start. It follows from the proved sharp population asymptotic. -/
theorem PowerProfile.left_populationG_envelope {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ M : ℝ, 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t → t ≤ 1 →
      populationG (w n) t ≤ M*(t^(1/alpha)+1/(n : ℝ)) := by
  obtain ⟨e, he, _, hea, K, hK, herr⟩ := hp.left_populationG_power_error
  have ha : 1 < alpha := hp.2.2.1.2.1
  have ha0 : 0 < alpha := by linarith
  have hg : 0 < 1-1/alpha := by
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  let A := Real.Gamma (1-1/alpha)*c^(1/alpha)
  have hA : 0 < A := mul_pos (Real.Gamma_pos_of_pos hg) (Real.rpow_pos_of_pos hp.2.2.1.1 _)
  refine ⟨A+K, add_pos hA hK, ?_⟩
  intro grid w hw n hn t ht ht1
  have hexp : 1/alpha ≤ 1/(alpha-e) :=
    (one_div_le_one_div_of_le (by linarith : 0 < alpha-e) (by linarith))
  have hpow := Real.rpow_le_rpow_of_exponent_ge ht ht1 hexp
  have hb := (abs_le.mp (herr grid w hw n hn t ht ht1)).2
  have hninv : 0 ≤ 1/(n : ℝ) := by positivity
  dsimp [A] at *
  nlinarith [mul_le_mul_of_nonneg_left hpow hK.le, mul_nonneg hA.le hninv]

end Luce.Section6
