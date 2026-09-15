import Luce.Section6Sampling

noncomputable section
namespace Luce.Section6

theorem relative_product_error {u v e a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) (he2 : e ≤ 2)
    (hu : |u-1| ≤ a*e) (hv : |v-1| ≤ b*e) :
    |u*v-1| ≤ (2*a*b+a+b)*e := by
  have hid : u*v-1 = (u-1)*(v-1)+(u-1)+(v-1) := by ring
  have hsq : e^2 ≤ 2*e := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (mul_nonneg ha hb)
  calc
    _ ≤ |u-1| * |v-1|+|u-1|+|v-1| := by
      rw [hid]
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le ((u-1)*(v-1)) (u-1)).trans_eq (by rw [abs_mul])) (le_refl _))
    _ ≤ (a*e)*(b*e)+a*e+b*e := add_le_add (add_le_add
      (mul_le_mul hu hv (abs_nonneg _) (mul_nonneg ha he)) hu) hv
    _ = (a*b)*e^2+(a+b)*e := by ring
    _ ≤ (a*b)*(2*e)+(a+b)*e := add_le_add hmul (le_refl _)
    _ = _ := by ring

end Luce.Section6
