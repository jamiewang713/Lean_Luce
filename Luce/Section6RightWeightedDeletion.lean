import Luce.Section6RightWeightedAsymptotic

noncomputable section
namespace Luce.Section6

/-- Bounded deletions preserve the right weighted-population asymptotic,
uniformly in deleted labels, with the original divisor n. -/
theorem PowerProfile.right_deletedD_relative_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) (r : ℕ) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ (removed : Finset (Fin n)), removed.card ≤ r →
    ∀ t : ℝ, 1 ≤ t →
    |deletedD (w n) removed 1 t /
        ((Real.Gamma (1+1/beta)*c^(-(1/beta))/beta)*t^(-1-1/beta)) - 1| ≤
      K*(t^(-(eta/beta)) + 1/((n : ℝ)*t^(-(1/beta)))) := by
  have hc : 0 < c := h.2.2.2.1.1
  have hb : 0 < beta := h.2.2.2.1.2.1
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
  let B := Real.Gamma (1+1/beta)*c^(-(1/beta))/beta
  have hB : 0 < B := div_pos (mul_pos hG (Real.rpow_pos_of_pos hc _)) hb
  let R := (r : ℝ)*Real.exp (-1)/B
  have hR : 0 ≤ R := div_nonneg (mul_nonneg (Nat.cast_nonneg r) (Real.exp_pos _).le) hB.le
  obtain ⟨K, hK, hbound⟩ := h.right_populationD_relative_error
  refine ⟨K+R, add_pos_of_pos_of_nonneg hK hR, ?_⟩
  intro grid w hw n hn removed hr t ht1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hp : 0 < t^(-1-1/beta) := Real.rpow_pos_of_pos ht _
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hd := populationD_one_deletion_bound (w n) removed hr ht
  have hrel := hbound grid w hw n hn t ht1
  change |populationD (w n) 1 t / (B*t^(-1-1/beta)) - 1| ≤ _ at hrel
  have hdiff : |deletedD (w n) removed 1 t / (B*t^(-1-1/beta)) -
      populationD (w n) 1 t / (B*t^(-1-1/beta))| ≤
      R*(1/((n : ℝ)*t^(-(1/beta)))) := by
    rw [← sub_div, abs_div, abs_of_pos (mul_pos hB hp), abs_sub_comm]
    calc
      _ ≤ ((r : ℝ)*(Real.exp (-1)/t)/(n : ℝ))/(B*t^(-1-1/beta)) :=
        div_le_div_of_nonneg_right hd (mul_pos hB hp).le
      _ = _ := by
        rw [← time_mul_weighted_power ht beta]
        dsimp [R]
        ring
  change |deletedD (w n) removed 1 t / (B*t^(-1-1/beta)) - 1| ≤ _
  calc
    _ ≤ |deletedD (w n) removed 1 t / (B*t^(-1-1/beta)) -
        populationD (w n) 1 t / (B*t^(-1-1/beta))| +
        |populationD (w n) 1 t / (B*t^(-1-1/beta)) - 1| := abs_sub_le _ _ _
    _ ≤ R*(1/((n : ℝ)*t^(-(1/beta)))) +
        K*(t^(-(eta/beta)) + 1/((n : ℝ)*t^(-(1/beta)))) := add_le_add hdiff hrel
    _ ≤ _ := by
      nlinarith [mul_nonneg hR (Real.rpow_pos_of_pos ht (-(eta/beta))).le]

end Luce.Section6
