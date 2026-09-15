import Luce.Section6ScaledEnvelopeSums

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace Luce.Section6

theorem linear_exp_absorption {x : ℝ} (hx : 0 ≤ x) :
    (1+8*x)*Real.exp (-(2*x)) ≤
      (1+8*Real.exp (-1))*Real.exp (-x) := by
  have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 := Real.mul_exp_neg_le_exp_neg_one x
  have h3 : (1+8*x)*Real.exp (-x) ≤ 1+8*Real.exp (-1) := by nlinarith
  have he : Real.exp (-(2*x)) = Real.exp (-x)*Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le

theorem populationD_one_eq_reflected_samples (grid : SamplingGrid) (w : WeightArray)
    (f : ℝ → ℝ) (hw : SampledRates grid w f) (n : ℕ) (t : ℝ) :
    populationD (w n) 1 t =
      (∑ i : Fin n, rateKernel t (f (1-samplePoint grid n i)))/(n : ℝ) := by
  have hsum : (∑ i : Fin n, rateKernel t ((w n).rate i)) =
      ∑ i : Fin n, rateKernel t (f (samplePoint grid n i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hw n i]
  have hrev := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
    (fun i : Fin n => rateKernel t (f (samplePoint grid n i)))
  change (∑ i : Fin n, rateKernel t (f (samplePoint grid n i.rev))) =
    ∑ i : Fin n, rateKernel t (f (samplePoint grid n i)) at hrev
  simp_rw [samplePoint_rev] at hrev
  simp only [populationD, pow_one]
  change (∑ i : Fin n, rateKernel t ((w n).rate i))/(n : ℝ) = _
  rw [hsum, ← hrev]

/-- Scaled weighted kernels have the same type of power envelope as
survivors. Far from the right endpoint only a lower rate bound is used. -/
theorem PowerProfile.right_scaled_rate_difference_bound {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ C d eps : ℝ, 0 < C ∧ 0 < d ∧ 0 < eps ∧ eps < 1 ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t : ℝ, 0 < t →
      |t*rateKernel t (f (1-s)) - t*rateKernel t (c*s^beta)| ≤
        C*t*s^(beta+eta)*survivalKernel t ((c/4)*s^beta) +
          2*Real.exp (-1)*(survivalKernel (t/2) d + survivalKernel (t/2) (c*eps^beta)) := by
  rcases h.2.2.2.1 with ⟨hc, hb, he, hex⟩
  obtain ⟨C0, hC0, hnear⟩ := hex.kernel_perturbation_bounds hc he
  obtain ⟨delta, hd, hdelta⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  change 0 < delta at hd
  let eps := min (delta/2) (1/4)
  have heps : 0 < eps := lt_min (by linarith) (by norm_num)
  have heps1 : eps < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hepsd : eps < delta := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨d, hd0, hoff⟩ := h.lower_away_right heps heps1
  let C := C0*(1+8*Real.exp (-1))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, d, eps, hC, hd0, heps, heps1, ?_⟩
  intro s hs t ht
  have henv : 0 ≤ C*t*s^(beta+eta)*survivalKernel t ((c/4)*s^beta) := by
    exact mul_nonneg (mul_nonneg (mul_pos hC ht).le (Real.rpow_pos_of_pos hs.1 _).le)
      (survivalKernel_pos _ _).le
  have htail : 0 ≤ 2*Real.exp (-1)*
      (survivalKernel (t/2) d + survivalKernel (t/2) (c*eps^beta)) := by
    exact mul_nonneg (by positivity) (add_nonneg (survivalKernel_pos _ _).le (survivalKernel_pos _ _).le)
  by_cases hsnear : s < eps
  · have hn := (hdelta ⟨hs.1, hsnear.trans hepsd⟩ t ht.le).2
    let x := (t*c*s^beta)/4
    have hx : 0 ≤ x := div_nonneg
      (mul_pos (mul_pos ht hc) (Real.rpow_pos_of_pos hs.1 _)).le (by norm_num)
    have ha : 1+t*(2*c*s^beta) = 1+8*x := by dsimp [x]; ring
    have hb' : -t*((c/2)*s^beta) = -(2*x) := by dsimp [x]; ring
    have hc' : -t*((c/4)*s^beta) = -x := by dsimp [x]; ring
    rw [survivalKernel, ha, hb'] at hn
    have hab := mul_le_mul_of_nonneg_left (linear_exp_absorption hx)
      (mul_nonneg hC0.le (Real.rpow_pos_of_pos hs.1 (beta+eta)).le)
    have hnear' : |rateKernel t (f (1-s))-rateKernel t (c*s^beta)| ≤
        C*s^(beta+eta)*Real.exp (-x) := by
      exact hn.trans (by dsimp [C]; nlinarith [hab])
    rw [← mul_sub, abs_mul, abs_of_pos ht]
    have hh := mul_le_mul_of_nonneg_left hnear' ht.le
    rw [survivalKernel, hc']
    nlinarith [hh]
  · have hsfar : eps ≤ s := le_of_not_gt hsnear
    have hflo : d ≤ f (1-s) := hoff (1-s) ⟨by linarith [hs.2], by linarith⟩
    have hplo : c*eps^beta ≤ c*s^beta :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow heps.le hsfar hb.le) hc.le
    have hfa := mul_le_mul_of_nonneg_left (rateKernel_bound_above_lower ht hflo) ht.le
    have hpa := mul_le_mul_of_nonneg_left (rateKernel_bound_above_lower ht hplo) ht.le
    have hid : t*(Real.exp (-1)/(t/2)) = 2*Real.exp (-1) := by field_simp
    rw [← mul_assoc, hid] at hfa hpa
    have hfn : 0 ≤ t*rateKernel t (f (1-s)) := mul_nonneg ht.le
      (rateKernel_nonneg (h.2.1 (1-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).le)
    have hpn : 0 ≤ t*rateKernel t (c*s^beta) := mul_nonneg ht.le
      (rateKernel_nonneg (mul_pos hc (Real.rpow_pos_of_pos hs.1 _)).le)
    have hab : |t*rateKernel t (f (1-s))-t*rateKernel t (c*s^beta)| ≤
        t*rateKernel t (f (1-s))+t*rateKernel t (c*s^beta) := by
      exact (abs_sub_le _ 0 _).trans_eq (by rw [sub_zero, zero_sub, abs_neg,
        abs_of_nonneg hfn, abs_of_nonneg hpn])
    nlinarith

end Luce.Section6
