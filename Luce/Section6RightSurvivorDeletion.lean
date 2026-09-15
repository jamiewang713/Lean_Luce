import Luce.Section6RightSurvivorRelative

noncomputable section
namespace Luce.Section6

/-- Uniformity of the right-survivor asymptotic under bounded deletions,
with the original divisor n retained. The deletion constant is proved
uniform in the labels rather than assumed. -/
theorem PowerProfile.right_deletedH_relative_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) (r : ℕ) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ (removed : Finset (Fin n)), removed.card ≤ r →
    ∀ t : ℝ, 1 ≤ t →
    |deletedH (w n) removed t /
        (Real.Gamma (1+1/beta)*c^(-(1/beta))*t^(-(1/beta))) - 1| ≤
      K*(t^(-(eta/beta)) + 1/((n : ℝ)*t^(-(1/beta)))) := by
  have hc : 0 < c := h.2.2.2.1.1
  have hb : 0 < beta := h.2.2.2.1.2.1
  have hG : 0 < Real.Gamma (1+1/beta) := Real.Gamma_pos_of_pos (by positivity)
  let A := Real.Gamma (1+1/beta)*c^(-(1/beta))
  have hA : 0 < A := mul_pos hG (Real.rpow_pos_of_pos hc _)
  obtain ⟨K, hK, hbound⟩ := h.right_populationH_relative_error
  have hrA : 0 ≤ (r : ℝ)/A := div_nonneg (Nat.cast_nonneg r) hA.le
  refine ⟨K+(r : ℝ)/A, add_pos_of_pos_of_nonneg hK hrA, ?_⟩
  intro grid w hw n hn removed hr t ht1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hp : 0 < t^(-(1/beta)) := Real.rpow_pos_of_pos ht _
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hd := populationH_deletion_bound (w n) removed hr ht.le
  have hrel := hbound grid w hw n hn t ht1
  change |populationH (w n) t / (A*t^(-(1/beta))) - 1| ≤ _ at hrel
  have hdiff : |deletedH (w n) removed t / (A*t^(-(1/beta))) -
      populationH (w n) t / (A*t^(-(1/beta)))| ≤
      ((r : ℝ)/A)*(1/((n : ℝ)*t^(-(1/beta)))) := by
    rw [← sub_div, abs_div, abs_of_pos (mul_pos hA hp), abs_sub_comm]
    calc
      _ ≤ ((r : ℝ)/(n : ℝ))/(A*t^(-(1/beta))) :=
        div_le_div_of_nonneg_right hd (mul_pos hA hp).le
      _ = _ := by ring
  change |deletedH (w n) removed t / (A*t^(-(1/beta))) - 1| ≤ _
  calc
    _ ≤ |deletedH (w n) removed t / (A*t^(-(1/beta))) -
        populationH (w n) t / (A*t^(-(1/beta)))| +
        |populationH (w n) t / (A*t^(-(1/beta))) - 1| := abs_sub_le _ _ _
    _ ≤ ((r : ℝ)/A)*(1/((n : ℝ)*t^(-(1/beta)))) +
        K*(t^(-(eta/beta)) + 1/((n : ℝ)*t^(-(1/beta)))) := add_le_add hdiff hrel
    _ ≤ _ := by
      nlinarith [mul_nonneg hrA (Real.rpow_pos_of_pos ht (-(eta/beta))).le]

end Luce.Section6
