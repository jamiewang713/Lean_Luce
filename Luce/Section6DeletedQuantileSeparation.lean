import Luce.Section6QuantileMeanSeparation

noncomputable section
namespace Luce.Section6

theorem scaled_deletion_error {n r : ℕ} (hn : 0 < n) {A B : ℝ}
    (h : |A-B| ≤ (r : ℝ)/n) : |(n : ℝ)*A-(n : ℝ)*B| ≤ r := by
  calc
    _ = (n : ℝ)*|A-B| := by rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    _ ≤ (n : ℝ)*((r : ℝ)/n) := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
    _ = _ := by field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]

/-- Actual deleted arrival means straddle the left quantile, with only
the proved finite deletion error r. The slope is chosen at most one. -/
theorem PowerProfile.left_deleted_quantile_separation {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ a delta M : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m r : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ u : ℝ, 0 < u → u ≤ 1/2 →
      (n : ℝ)*deletedG (w n) removed ((1-u)*leftQuantileTime (w n) m) ≤
        (m : ℝ)-a*u*m+r ∧
      (m : ℝ)+a*u*m-r ≤
        (n : ℝ)*deletedG (w n) removed ((1+u)*leftQuantileTime (w n) m) := by
  obtain ⟨a, delta, M, ha, hd, hM, hsep⟩ := hp.left_quantile_mean_separation
  refine ⟨min a 1, delta, M, lt_min ha zero_lt_one, min_le_right _ _, hd, hM, ?_⟩
  intro grid w hw n m r hm hmn hlarge hsmall removed hr u hu hu1
  have hn := hm.trans hmn
  have ht := (leftQuantileTime_spec (w n) hm hmn).1
  have hc : (n : ℝ)*populationG (w n) (leftQuantileTime (w n) m) = m := by
    rw [(leftQuantileTime_spec (w n) hm hmn).2]
    field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  have hs := hsep grid w hw n m hm hmn hlarge hsmall u hu hu1
  have hl := scaled_deletion_error hn (populationG_deletion_bound (w n) removed hr
    (mul_nonneg (by linarith : 0 ≤ 1-u) ht.le))
  have hh := scaled_deletion_error hn (populationG_deletion_bound (w n) removed hr
    (show 0 ≤ (1+u)*leftQuantileTime (w n) m by positivity))
  have hweak : min a 1*u*(m : ℝ) ≤ a*u*m :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hu.le) (Nat.cast_nonneg m)
  have hl' := (abs_le.mp hl).1
  have hh' := (abs_le.mp hh).2
  constructor <;> nlinarith only [hs.1, hs.2, hc, hl', hh', hweak]

/-- Actual deleted survivor means straddle the right quantile. This uses
the small survivor population and retains the original divisor n. -/
theorem PowerProfile.right_deleted_quantile_separation {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ a delta M : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m r : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ u : ℝ, 0 < u → u ≤ 1/2 →
      (m : ℝ)+a*u*m-r ≤
        (n : ℝ)*deletedH (w n) removed ((1-u)*rightQuantileTime (w n) m) ∧
      (n : ℝ)*deletedH (w n) removed ((1+u)*rightQuantileTime (w n) m) ≤
        (m : ℝ)-a*u*m+r := by
  obtain ⟨a, delta, M, ha, hd, hM, hsep⟩ := hp.right_quantile_mean_separation
  refine ⟨min a 1, delta, M, lt_min ha zero_lt_one, min_le_right _ _, hd, hM, ?_⟩
  intro grid w hw n m r hm hmn hlarge hsmall removed hr u hu hu1
  have hn := hm.trans hmn
  have ht := (rightQuantileTime_spec (w n) hm hmn).1
  have hc : (n : ℝ)*populationH (w n) (rightQuantileTime (w n) m) = m := by
    rw [(rightQuantileTime_spec (w n) hm hmn).2]
    field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  have hs := hsep grid w hw n m hm hmn hlarge hsmall u hu hu1
  have hl := scaled_deletion_error hn (populationH_deletion_bound (w n) removed hr
    (mul_nonneg (by linarith : 0 ≤ 1-u) ht.le))
  have hh := scaled_deletion_error hn (populationH_deletion_bound (w n) removed hr
    (show 0 ≤ (1+u)*rightQuantileTime (w n) m by positivity))
  have hweak : min a 1*u*(m : ℝ) ≤ a*u*m :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hu.le) (Nat.cast_nonneg m)
  have hl' := (abs_le.mp hl).2
  have hh' := (abs_le.mp hh).1
  constructor <;> nlinarith only [hs.1, hs.2, hc, hl', hh', hweak]

end Luce.Section6
