import Luce.Section6EnvelopeSums

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Luce.Section6

theorem populationH_eq_reflected_samples (grid : SamplingGrid) (w : WeightArray)
    (f : ℝ → ℝ) (hw : SampledRates grid w f) (n : ℕ) (t : ℝ) :
    populationH (w n) t =
      (∑ i : Fin n, survivalKernel t (f (1-samplePoint grid n i)))/(n : ℝ) := by
  have hsum : (∑ i : Fin n, survivalKernel t ((w n).rate i)) =
      ∑ i : Fin n, survivalKernel t (f (samplePoint grid n i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hw n i]
  have hrev := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
    (fun i : Fin n => survivalKernel t (f (samplePoint grid n i)))
  change (∑ i : Fin n, survivalKernel t (f (samplePoint grid n i.rev))) =
    ∑ i : Fin n, survivalKernel t (f (samplePoint grid n i)) at hrev
  simp_rw [samplePoint_rev] at hrev
  unfold populationH
  rw [hsum, ← hrev]

/-- A global pointwise comparison derived from the actual profile inputs.
The two tail terms cover the complement of the small right neighborhood. -/
theorem PowerProfile.right_survival_difference_bound {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ C d eps : ℝ, 0 < C ∧ 0 < d ∧ 0 < eps ∧ eps < 1 ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t : ℝ, 0 ≤ t →
      |survivalKernel t (f (1-s)) - survivalKernel t (c*s^beta)| ≤
        C*t*s^(beta+eta)*survivalKernel t ((c/2)*s^beta) +
          survivalKernel t d + survivalKernel t (c*eps^beta) := by
  rcases h.2.2.2.1 with ⟨hc, hb, he, hex⟩
  obtain ⟨C, hC, hnear⟩ := hex.kernel_perturbation_bounds hc he
  obtain ⟨delta, hd, hdelta⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  change 0 < delta at hd
  let eps := min (delta/2) (1/4)
  have heps : 0 < eps := lt_min (by linarith) (by norm_num)
  have heps1 : eps < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hepsd : eps < delta := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨d, hd0, hoff⟩ := h.lower_away_right heps heps1
  refine ⟨C, d, eps, hC, hd0, heps, heps1, ?_⟩
  intro s hs t ht
  have henv : 0 ≤ C*t*s^(beta+eta)*survivalKernel t ((c/2)*s^beta) := by
    apply mul_nonneg _ (survivalKernel_pos _ _).le
    exact mul_nonneg (mul_nonneg hC.le ht) (Real.rpow_pos_of_pos hs.1 _).le
  by_cases hsnear : s < eps
  · have hn := (hdelta ⟨hs.1, hsnear.trans hepsd⟩ t ht).1
    linarith [(survivalKernel_pos t d), (survivalKernel_pos t (c*eps^beta))]
  · have hsfar : eps ≤ s := le_of_not_gt hsnear
    have hflo : d ≤ f (1-s) := hoff (1-s) ⟨by linarith [hs.2], by linarith⟩
    have hplo : c*eps^beta ≤ c*s^beta :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow heps.le hsfar hb.le) hc.le
    have hfa : survivalKernel t (f (1-s)) ≤ survivalKernel t d := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hflo (neg_nonpos.mpr ht)
    have hpa : survivalKernel t (c*s^beta) ≤ survivalKernel t (c*eps^beta) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hplo (neg_nonpos.mpr ht)
    have hab : |survivalKernel t (f (1-s))-survivalKernel t (c*s^beta)| ≤
        survivalKernel t (f (1-s))+survivalKernel t (c*s^beta) := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_of_pos (survivalKernel_pos _ _)] using
        abs_sub_le (survivalKernel t (f (1-s))) 0 (survivalKernel t (c*s^beta))
    linarith

/-- Actual sampled-profile survivor population versus the power prototype.
All constants and the neighborhood are constructed from the profile. -/
theorem PowerProfile.right_populationH_comparison {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (h : PowerProfile f left (.power c beta eta)) :
    ∃ C d eps : ℝ, 0 < C ∧ 0 < d ∧ 0 < eps ∧ eps < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t →
    |populationH (w n) t -
      (∑ i : Fin n, Real.exp (-((c*t)*(samplePoint grid n i)^beta)))/(n : ℝ)| ≤
      C*t*(1/(c*t/4))^((beta+eta)/beta)*
        ((1/(c*t/4))^(1/beta)*Real.Gamma (1+1/beta) + 1/(n : ℝ)) +
      survivalKernel t d + survivalKernel t (c*eps^beta) := by
  have hc := h.2.2.2.1.1
  have hb := h.2.2.2.1.2.1
  have he := h.2.2.2.1.2.2.1
  obtain ⟨C0, d, eps, hC0, hd, heps, heps1, hdiff⟩ := h.right_survival_difference_bound
  obtain ⟨C1, hC1, hsum⟩ := power_envelope_average_bound hb
    (a := beta+eta) (by positivity)
  refine ⟨C0*C1, d, eps, mul_pos hC0 hC1, hd, heps, heps1, ?_⟩
  intro grid w hw n hn t ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let s : Fin n → ℝ := samplePoint grid n
  let E : Fin n → ℝ := fun i => (s i)^(beta+eta)*Real.exp (-((c*t/2)*(s i)^beta))
  have hE := hsum grid n hn (c*t/2) (by positivity)
  have hr : (c*t/2)/2 = c*t/4 := by ring
  rw [hr] at hE
  have hterm (i : Fin n) :
      |survivalKernel t (f (1-s i)) - Real.exp (-((c*t)*(s i)^beta))| ≤
        C0*t*E i + survivalKernel t d + survivalKernel t (c*eps^beta) := by
    have hh := hdiff (s i) (samplePoint_mem grid i) t ht.le
    have ha : -t*(c*(s i)^beta) = -((c*t)*(s i)^beta) := by ring
    have hb' : -t*((c/2)*(s i)^beta) = -((c*t/2)*(s i)^beta) := by ring
    simpa only [survivalKernel, ha, hb', E, mul_assoc] using hh
  rw [populationH_eq_reflected_samples grid w f hw n t, ← sub_div,
    abs_div, abs_of_pos hnR]
  calc
    _ ≤ (∑ i : Fin n,
        |survivalKernel t (f (1-s i)) - Real.exp (-((c*t)*(s i)^beta))|)/(n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ i : Fin n, (C0*t*E i + survivalKernel t d +
        survivalKernel t (c*eps^beta)))/(n : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hterm i) hnR.le
    _ = C0*t*((∑ i, E i)/(n : ℝ)) + survivalKernel t d + survivalKernel t (c*eps^beta) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_div,
        mul_div_cancel_left₀ _ hnR.ne']
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hE (mul_nonneg hC0.le ht.le)
      dsimp only [E, s]
      nlinarith [hh]

end Luce.Section6
