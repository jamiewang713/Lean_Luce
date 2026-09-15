import Luce.Section6LeftArrivalAsymptotic

noncomputable section
namespace Luce.Section6

theorem PowerProfile.left_deletedG_relative_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) (r : ℕ) :
    ∃ zeta K : ℝ, 0 < zeta ∧ 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ (removed : Finset (Fin n)), removed.card ≤ r →
    ∀ t : ℝ, 0 < t → t ≤ 1 →
    |deletedG (w n) removed t /
        (Real.Gamma (1-1/alpha)*c^(1/alpha)*t^(1/alpha)) - 1| ≤
      K*(t^zeta+1/((n : ℝ)*t^(1/alpha))) := by
  have hc := h.2.2.1.1
  have ha := h.2.2.1.2.1
  have hg : 0 < 1-1/alpha := by
    have hh := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hh
    linarith
  let A := Real.Gamma (1-1/alpha)*c^(1/alpha)
  have hA : 0 < A := mul_pos (Real.Gamma_pos_of_pos hg) (Real.rpow_pos_of_pos hc _)
  obtain ⟨zeta, K, hz, hK, hbound⟩ := h.left_populationG_relative_error
  have hrA : 0 ≤ (r : ℝ)/A := div_nonneg (Nat.cast_nonneg r) hA.le
  refine ⟨zeta, K+(r : ℝ)/A, hz, add_pos_of_pos_of_nonneg hK hrA, ?_⟩
  intro grid w hw n hn removed hr t ht ht1
  have hp : 0 < t^(1/alpha) := Real.rpow_pos_of_pos ht _
  have hd := populationG_deletion_bound (w n) removed hr ht.le
  have hrel := hbound grid w hw n hn t ht ht1
  change |populationG (w n) t / (A*t^(1/alpha)) - 1| ≤ _ at hrel
  have hdiff : |deletedG (w n) removed t / (A*t^(1/alpha)) -
      populationG (w n) t / (A*t^(1/alpha))| ≤
      ((r : ℝ)/A)*(1/((n : ℝ)*t^(1/alpha))) := by
    rw [← sub_div, abs_div, abs_of_pos (mul_pos hA hp), abs_sub_comm]
    calc
      _ ≤ ((r : ℝ)/(n : ℝ))/(A*t^(1/alpha)) :=
        div_le_div_of_nonneg_right hd (mul_pos hA hp).le
      _ = _ := by ring
  change |deletedG (w n) removed t / (A*t^(1/alpha)) - 1| ≤ _
  calc
    _ ≤ |deletedG (w n) removed t / (A*t^(1/alpha)) -
        populationG (w n) t / (A*t^(1/alpha))| +
        |populationG (w n) t / (A*t^(1/alpha)) - 1| := abs_sub_le _ _ _
    _ ≤ ((r : ℝ)/A)*(1/((n : ℝ)*t^(1/alpha))) +
        K*(t^zeta+1/((n : ℝ)*t^(1/alpha))) := add_le_add hdiff hrel
    _ ≤ _ := by nlinarith [mul_nonneg hrA (Real.rpow_pos_of_pos ht zeta).le]

end Luce.Section6
