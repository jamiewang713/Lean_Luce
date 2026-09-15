import Luce.Section6PopulationFinite

noncomputable section
namespace Luce.Section6

/-- A deletion/rank error small compared with the window's mean separation
gives both relative thresholds. This is a numerical lemma, not a model input. -/
theorem relative_mean_separation {m v R q low high : ℝ}
    (hm : 0 ≤ m) (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hR : R ≤ v*m/8) (hq : |q-m| ≤ R)
    (hlow : low ≤ m-v*m+R) (hhigh : m+v*m-R ≤ high) :
    (1+v/8)*low ≤ q ∧ q ≤ (1-v/8)*high := by
  have hvm := mul_nonneg hv hm
  have hqlo := (abs_le.mp hq).1
  have hqhi := (abs_le.mp hq).2
  have hlm : low ≤ m := by linarith only [hlow, hR, hvm]
  have hlmul := mul_le_mul_of_nonneg_left hlm (div_nonneg hv (by norm_num : (0 : ℝ) ≤ 8))
  have hhm : m+v*m/2 ≤ high := by linarith only [hhigh, hR, hvm]
  have hcoef : 0 ≤ 1-v/8 := by linarith only [hv1]
  have hhmul := mul_le_mul_of_nonneg_left hhm hcoef
  have hvvm := mul_le_mul_of_nonneg_right hv1 hvm
  constructor
  · nlinarith only [hlow, hR, hqlo, hlmul, hvm]
  · nlinarith only [hqhi, hR, hhmul, hvvm, hvm]

end Luce.Section6
