import Luce.Section6FastProfileComparison
import Luce.Section6WeightedProfileComparison

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

theorem PowerProfile.left_scaled_rate_difference_bound {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) :
    ∃ eta' : ℝ, 0 < eta' ∧ eta' < eta ∧ eta' < alpha-1 ∧
    ∃ C M : ℝ, 0 < C ∧ 0 < M ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t : ℝ, 0 < t →
      |t*rateKernel t (f s)-t*rateKernel t (c*s^(-alpha))| ≤
        C*t*s^(-alpha+eta')*survivalKernel t ((c/4)*s^(-alpha)) + t*M := by
  rcases h.2.2.1 with ⟨hc, ha, he, hex⟩
  obtain ⟨eta', he', heeta, healpha, hex'⟩ := hex.exists_fast_error_exponent ha he
  obtain ⟨C0, hC0, hnear⟩ := hex'.kernel_perturbation_bounds hc he'
  obtain ⟨delta, hd, hdelta⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  change 0 < delta at hd
  let eps := min (delta/2) (1/4)
  have heps : 0 < eps := lt_min (by linarith) (by norm_num)
  have heps1 : eps < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hepsd : eps < delta := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨M, hM, hoff⟩ := h.upper_away_left heps heps1
  let C := C0*(1+8*Real.exp (-1))
  have hC : 0 < C := by dsimp [C]; positivity
  have hM' : 0 < M+c*eps^(-alpha) := add_pos hM (mul_pos hc (Real.rpow_pos_of_pos heps _))
  refine ⟨eta', he', heeta, healpha, C, M+c*eps^(-alpha), hC, hM', ?_⟩
  intro s hs t ht
  have henv : 0 ≤ C*t*s^(-alpha+eta')*survivalKernel t ((c/4)*s^(-alpha)) :=
    mul_nonneg (mul_nonneg (mul_pos hC ht).le (Real.rpow_pos_of_pos hs.1 _).le)
      (survivalKernel_pos _ _).le
  by_cases hsnear : s < eps
  · have hn := (hdelta ⟨hs.1, hsnear.trans hepsd⟩ t ht.le).2
    let x := (t*c*s^(-alpha))/4
    have hx : 0 ≤ x := div_nonneg
      (mul_pos (mul_pos ht hc) (Real.rpow_pos_of_pos hs.1 _)).le (by norm_num)
    have ha' : 1+t*(2*c*s^(-alpha)) = 1+8*x := by dsimp [x]; ring
    have hb' : -t*((c/2)*s^(-alpha)) = -(2*x) := by dsimp [x]; ring
    have hc' : -t*((c/4)*s^(-alpha)) = -x := by dsimp [x]; ring
    rw [survivalKernel, ha', hb'] at hn
    have hab := mul_le_mul_of_nonneg_left (linear_exp_absorption hx)
      (mul_nonneg hC0.le (Real.rpow_pos_of_pos hs.1 (-alpha+eta')).le)
    have hnear' : |rateKernel t (f s)-rateKernel t (c*s^(-alpha))| ≤
        C*s^(-alpha+eta')*Real.exp (-x) := by
      exact hn.trans (by dsimp [C]; nlinarith [hab])
    rw [← mul_sub, abs_mul, abs_of_pos ht]
    have hh := mul_le_mul_of_nonneg_left hnear' ht.le
    rw [survivalKernel, hc']
    nlinarith [mul_nonneg ht.le hM'.le]
  · have hsfar : eps ≤ s := le_of_not_gt hsnear
    have hfhi : f s ≤ M := hoff s ⟨hsfar, hs.2⟩
    have hphi : c*s^(-alpha) ≤ c*eps^(-alpha) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos heps hsfar (by linarith)) hc.le
    have hfn := rateKernel_nonneg (t := t) (h.2.1 s hs).le
    have hpn := rateKernel_nonneg (t := t) (mul_pos hc (Real.rpow_pos_of_pos hs.1 (-alpha))).le
    have hfb : rateKernel t (f s) ≤ M := by
      have hh := mul_le_mul_of_nonneg_left (survivalKernel_le_one ht.le (h.2.1 s hs).le) (h.2.1 s hs).le
      exact (by simpa only [rateKernel, mul_one] using hh : rateKernel t (f s) ≤ f s).trans hfhi
    have hpb : rateKernel t (c*s^(-alpha)) ≤ c*eps^(-alpha) := by
      have hp := (mul_pos hc (Real.rpow_pos_of_pos hs.1 (-alpha))).le
      have hh := mul_le_mul_of_nonneg_left (survivalKernel_le_one ht.le hp) hp
      exact (by simpa only [rateKernel, mul_one] using hh : rateKernel t (c*s^(-alpha)) ≤ c*s^(-alpha)).trans hphi
    have hab : |t*rateKernel t (f s)-t*rateKernel t (c*s^(-alpha))| ≤
        t*rateKernel t (f s)+t*rateKernel t (c*s^(-alpha)) := by
      exact (abs_sub_le _ 0 _).trans_eq (by rw [sub_zero, zero_sub, abs_neg,
        abs_of_nonneg (mul_nonneg ht.le hfn), abs_of_nonneg (mul_nonneg ht.le hpn)])
    have hh1 := mul_le_mul_of_nonneg_left hfb ht.le
    have hh2 := mul_le_mul_of_nonneg_left hpb ht.le
    nlinarith

end Luce.Section6
