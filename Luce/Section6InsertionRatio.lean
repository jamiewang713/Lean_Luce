import Luce.Section6SampledRateUpper

noncomputable section
namespace Luce.Section6

theorem right_insertion_ratio_identity {K C n a h beta : ℝ}
    (hC : 0 < C) (hn : 0 < n) (ha : 0 < a) (hh : 0 < h) :
    K*(a/n)^beta/(C*n^(-beta)*h^(beta+1)) = (K/C)*((a/h)^beta/h) := by
  rw [Real.div_rpow ha.le hn.le, Real.div_rpow ha.le hh.le,
    Real.rpow_neg hn.le, Real.rpow_add hh, Real.rpow_one]
  field_simp [ne_of_gt hC, ne_of_gt hh, ne_of_gt (Real.rpow_pos_of_pos hn beta),
    ne_of_gt (Real.rpow_pos_of_pos hh beta)]

theorem left_insertion_ratio_identity {K C n a h alpha : ℝ}
    (hC : 0 < C) (hn : 0 < n) (ha : 0 < a) (hh : 0 < h) :
    K*(a/n)^(-alpha)/(C*n^alpha*h^(1-alpha)) = (K/C)*((h/a)^alpha/h) := by
  rw [Real.div_rpow ha.le hn.le, Real.div_rpow hh.le ha.le,
    Real.rpow_neg ha.le, Real.rpow_neg hn.le,
    show (1-alpha : ℝ) = 1+(-alpha) by ring,
    Real.rpow_add hh, Real.rpow_one, Real.rpow_neg hh.le]
  field_simp [ne_of_gt hC, ne_of_gt hh, ne_of_gt (Real.rpow_pos_of_pos hn alpha),
    ne_of_gt (Real.rpow_pos_of_pos ha alpha), ne_of_gt (Real.rpow_pos_of_pos hh alpha)]

end Luce.Section6
