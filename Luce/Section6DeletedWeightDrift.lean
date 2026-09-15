import Luce.Section6QuantileWeightStability

noncomputable section
open Set
namespace Luce.Section6

/-- Absolute deterministic variation from the actual second-moment bound. -/
theorem populationD_absolute_variation {n : ℕ} (w : Weights n) (hn : 0 < n)
    {C m t s : ℝ} (ht : 0 < t)
    (hsecond : ∀ x ∈ Icc (t/4) (4*t), (n : ℝ)*populationD w 2 x ≤ C*m/t^2)
    (hs : s ∈ Icc (t/4) (4*t)) :
    |(n : ℝ)*populationD w 1 s-(n : ℝ)*populationD w 1 t| ≤ C*m/t^2*|s-t| := by
  have hderiv (x : ℝ) (_hx : x ∈ Icc (t/4) (4*t)) :
      HasDerivWithinAt (fun y => (n : ℝ)*populationD w 1 y)
        ((n : ℝ)*(-populationD w 2 x)) (Icc (t/4) (4*t)) x :=
    ((populationD_hasDerivAt w 1 x).const_mul (n : ℝ)).hasDerivWithinAt
  have hnorm (x : ℝ) (hx : x ∈ Icc (t/4) (4*t)) :
      ‖(n : ℝ)*(-populationD w 2 x)‖ ≤ C*m/t^2 := by
    rw [mul_neg, norm_neg, Real.norm_eq_abs,
      abs_of_pos (mul_pos (Nat.cast_pos.mpr hn) (populationD_pos hn w 2 x))]
    exact hsecond x hx
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (t/4) (4*t)).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hnorm
      (show t ∈ Icc (t/4) (4*t) by constructor <;> linarith) hs

/-- Drift from a deleted endpoint mean to the original central mean.
Deletion and time variation are both proved; the finite second-moment
premise is supplied by the existing profile moment theorem. -/
theorem deleted_weight_mean_drift {n r : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (hr : removed.card ≤ r) {C m t s u : ℝ}
    (hC : 0 ≤ C) (hm : 0 ≤ m) (ht : 0 < t)
    (hsecond : ∀ x ∈ Icc (t/4) (4*t), (n : ℝ)*populationD w 2 x ≤ C*m/t^2)
    (hs : s ∈ Icc (t/2) (2*t)) (hdist : |s-t| ≤ u*t) :
    |(n : ℝ)*deletedD w removed 1 s-(n : ℝ)*populationD w 1 t| ≤
      C*u*m/t+2*(r : ℝ)/t := by
  have hspos : 0 < s := (half_pos ht).trans_le hs.1
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hd := populationD_one_deletion_bound w removed hr hspos
  have hdR : |(n : ℝ)*populationD w 1 s-(n : ℝ)*deletedD w removed 1 s| ≤
      (r : ℝ)*(Real.exp (-1)/s) := by
    calc
      _ = (n : ℝ)*|populationD w 1 s-deletedD w removed 1 s| := by
        rw [← mul_sub, abs_mul, abs_of_pos hnR]
      _ ≤ (n : ℝ)*((r : ℝ)*(Real.exp (-1)/s)/n) := mul_le_mul_of_nonneg_left hd hnR.le
      _ = _ := by field_simp
  have he : Real.exp (-1)/s ≤ 2/t := by
    apply (div_le_div_iff₀ hspos ht).mpr
    have he1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_right he1 ht.le, hs.1]
  have hdel : |(n : ℝ)*deletedD w removed 1 s-(n : ℝ)*populationD w 1 s| ≤ 2*(r : ℝ)/t := by
    rw [abs_sub_comm]
    exact hdR.trans ((mul_le_mul_of_nonneg_left he (Nat.cast_nonneg r)).trans_eq (by ring))
  have hv := populationD_absolute_variation w hn ht hsecond
    (show s ∈ Icc (t/4) (4*t) by constructor <;> linarith [hs.1, hs.2])
  have hvar : |(n : ℝ)*populationD w 1 s-(n : ℝ)*populationD w 1 t| ≤ C*u*m/t := by
    calc
      _ ≤ C*m/t^2*|s-t| := hv
      _ ≤ C*m/t^2*(u*t) := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = _ := by field_simp
  exact (abs_sub_le _ ((n : ℝ)*populationD w 1 s) _).trans
    ((add_le_add hdel hvar).trans_eq (add_comm _ _))

end Luce.Section6
