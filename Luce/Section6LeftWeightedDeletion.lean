import Luce.Section6LeftWeightedAsymptotic

noncomputable section
namespace Luce.Section6

theorem PowerProfile.left_deletedD_relative_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) (r : ℕ) :
    ∃ zeta K : ℝ, 0 < zeta ∧ 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ (removed : Finset (Fin n)), removed.card ≤ r →
    ∀ t : ℝ, 0 < t → t ≤ 1 →
    |deletedD (w n) removed 1 t /
        ((Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha)*t^(1/alpha-1)) - 1| ≤
      K*(t^zeta+1/((n : ℝ)*t^(1/alpha))) := by
  have hc := h.2.2.1.1
  have ha := h.2.2.1.2.1
  have hg : 0 < 1-1/alpha := by
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  let B := Real.Gamma (1-1/alpha)*c^(1/alpha)/alpha
  have hB : 0 < B := div_pos (mul_pos (Real.Gamma_pos_of_pos hg) (Real.rpow_pos_of_pos hc _))
    (zero_lt_one.trans ha)
  let R := (r : ℝ)*Real.exp (-1)/B
  have hR : 0 ≤ R := div_nonneg (mul_nonneg (Nat.cast_nonneg r) (Real.exp_pos _).le) hB.le
  obtain ⟨zeta, K, hz, hK, hbound⟩ := h.left_populationD_relative_error
  refine ⟨zeta, K+R, hz, add_pos_of_pos_of_nonneg hK hR, ?_⟩
  intro grid w hw n hn removed hr t ht ht1
  have hp : 0 < t^(1/alpha-1) := Real.rpow_pos_of_pos ht _
  have hd := populationD_one_deletion_bound (w n) removed hr ht
  have hrel := hbound grid w hw n hn t ht ht1
  change |populationD (w n) 1 t / (B*t^(1/alpha-1)) - 1| ≤ _ at hrel
  have hdiff : |deletedD (w n) removed 1 t / (B*t^(1/alpha-1)) -
      populationD (w n) 1 t / (B*t^(1/alpha-1))| ≤
      R*(1/((n : ℝ)*t^(1/alpha))) := by
    rw [← sub_div, abs_div, abs_of_pos (mul_pos hB hp), abs_sub_comm]
    calc
      _ ≤ ((r : ℝ)*(Real.exp (-1)/t)/(n : ℝ))/(B*t^(1/alpha-1)) :=
        div_le_div_of_nonneg_right hd (mul_pos hB hp).le
      _ = _ := by
        rw [← time_mul_fast_weighted_power ht alpha]
        dsimp [R]
        ring
  change |deletedD (w n) removed 1 t / (B*t^(1/alpha-1)) - 1| ≤ _
  calc
    _ ≤ |deletedD (w n) removed 1 t / (B*t^(1/alpha-1)) -
        populationD (w n) 1 t / (B*t^(1/alpha-1))| +
        |populationD (w n) 1 t / (B*t^(1/alpha-1)) - 1| := abs_sub_le _ _ _
    _ ≤ R*(1/((n : ℝ)*t^(1/alpha)))+K*(t^zeta+1/((n : ℝ)*t^(1/alpha))) :=
      add_le_add hdiff hrel
    _ ≤ _ := by nlinarith [mul_nonneg hR (Real.rpow_pos_of_pos ht zeta).le]

end Luce.Section6
