import Luce.Section6LeftOrdinaryWeightedRow

noncomputable section
namespace Luce.Section6

/-- Transfer an ordinary weighted kernel through a two-sided rate-time
comparison. Concrete applications must prove both comparison premises. -/
theorem weighted_rate_kernel_comparison {w h u v b B d : ℝ}
    (hw : 0 ≤ w) (hh : 0 < h) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hB : 0 ≤ B) (hd : 0 ≤ d) (hlower : b*v ≤ u) (hupper : u ≤ B*v) :
    w*(u/h)*Real.exp (-(d*u)) ≤ B*(w*(v/h)*Real.exp (-((d*b)*v))) := by
  have hp : w*(u/h) ≤ B*(w*(v/h)) := by
    have he := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hupper hh.le) hw
    exact he.trans_eq (by ring)
  have hex : Real.exp (-(d*u)) ≤ Real.exp (-((d*b)*v)) := by
    apply Real.exp_le_exp.mpr
    have he := mul_le_mul_of_nonneg_left hlower hd
    nlinarith only [he]
  have he := mul_le_mul hp hex (Real.exp_pos _).le (by positivity)
  simpa only [mul_assoc] using he

end Luce.Section6
