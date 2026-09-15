import Luce.Section6FastErrorExponent
import Luce.Section6FastArrivalBounds
import Luce.Section6InactiveBounds

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

/-- Actual fast-arrival kernels are controlled by an integrable power
envelope and an O(t) off-endpoint term. The smaller error exponent and all
bounds are derived from the original profile. -/
theorem PowerProfile.left_arrival_difference_bound {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) :
    ∃ eta' : ℝ, 0 < eta' ∧ eta' < eta ∧ eta' < alpha-1 ∧
    ∃ C M : ℝ, 0 < C ∧ 0 < M ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t : ℝ, 0 ≤ t →
      |(1-survivalKernel t (f s)) - (1-survivalKernel t (c*s^(-alpha)))| ≤
        C*t*s^(-alpha+eta')*survivalKernel t ((c/2)*s^(-alpha)) + t*M := by
  rcases h.2.2.1 with ⟨hc, ha, he, hex⟩
  obtain ⟨eta', he', heeta, healpha, hex'⟩ := hex.exists_fast_error_exponent ha he
  obtain ⟨C, hC, hnear⟩ := hex'.kernel_perturbation_bounds hc he'
  obtain ⟨delta, hd, hdelta⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  change 0 < delta at hd
  let eps := min (delta/2) (1/4)
  have heps : 0 < eps := lt_min (by linarith) (by norm_num)
  have heps1 : eps < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hepsd : eps < delta := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨M, hM, hoff⟩ := h.upper_away_left heps heps1
  have hM' : 0 < M+c*eps^(-alpha) := add_pos hM (mul_pos hc (Real.rpow_pos_of_pos heps _))
  refine ⟨eta', he', heeta, healpha, C, M+c*eps^(-alpha), hC, hM', ?_⟩
  intro s hs t ht
  have henv : 0 ≤ C*t*s^(-alpha+eta')*survivalKernel t ((c/2)*s^(-alpha)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le ht) (Real.rpow_pos_of_pos hs.1 _).le)
      (survivalKernel_pos _ _).le
  by_cases hsnear : s < eps
  · have hn := (hdelta ⟨hs.1, hsnear.trans hepsd⟩ t ht).1
    have heq : (1-survivalKernel t (f s)) - (1-survivalKernel t (c*s^(-alpha))) =
        -(survivalKernel t (f s)-survivalKernel t (c*s^(-alpha))) := by ring
    rw [heq, abs_neg]
    exact hn.trans (le_add_of_nonneg_right (mul_nonneg ht hM'.le))
  · have hsfar : eps ≤ s := le_of_not_gt hsnear
    have hfhi : f s ≤ M := hoff s ⟨hsfar, hs.2⟩
    have hphi : c*s^(-alpha) ≤ c*eps^(-alpha) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos heps hsfar (by linarith)) hc.le
    have hfa := one_sub_exp_neg_bounds (mul_nonneg ht (h.2.1 s hs).le)
    have hpa := one_sub_exp_neg_bounds
      (mul_nonneg ht (mul_pos hc (Real.rpow_pos_of_pos hs.1 (-alpha))).le)
    have hfn : 0 ≤ 1-survivalKernel t (f s) := by
      simpa only [survivalKernel, neg_mul] using hfa.1
    have hpn : 0 ≤ 1-survivalKernel t (c*s^(-alpha)) := by
      simpa only [survivalKernel, neg_mul] using hpa.1
    have hfb : 1-survivalKernel t (f s) ≤ t*M := by
      have hh : 1-survivalKernel t (f s) ≤ t*f s := by
        simpa only [survivalKernel, neg_mul] using hfa.2.2
      exact hh.trans (mul_le_mul_of_nonneg_left hfhi ht)
    have hpb : 1-survivalKernel t (c*s^(-alpha)) ≤ t*(c*eps^(-alpha)) := by
      have hh : 1-survivalKernel t (c*s^(-alpha)) ≤ t*(c*s^(-alpha)) := by
        simpa only [survivalKernel, neg_mul] using hpa.2.2
      exact hh.trans (mul_le_mul_of_nonneg_left hphi ht)
    have hab : |(1-survivalKernel t (f s)) - (1-survivalKernel t (c*s^(-alpha)))| ≤
        (1-survivalKernel t (f s)) + (1-survivalKernel t (c*s^(-alpha))) := by
      exact (abs_sub_le _ 0 _).trans_eq (by rw [sub_zero, zero_sub, abs_neg,
        abs_of_nonneg hfn, abs_of_nonneg hpn])
    nlinarith

end Luce.Section6
