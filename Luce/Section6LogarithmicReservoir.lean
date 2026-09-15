import Luce.Section6SurvivorReservoir

noncomputable section
namespace Luce.Section6

theorem logarithmic_survival_sqrt_identity {n m : ℝ} (hn : 0 < n) (hm : 0 < m) :
    n*Real.exp (-(1/2 : ℝ)*Real.log (n/m)) = Real.sqrt (n*m) := by
  have he : (n*Real.exp (-(1/2 : ℝ)*Real.log (n/m)))^2 = n*m := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ)*(-(1/2 : ℝ)*Real.log (n/m)) = -Real.log (n/m) by ring]
    rw [Real.exp_neg, Real.exp_log (div_pos hn hm)]
    field_simp
    <;> ring
  have hs := Real.sq_sqrt (mul_nonneg hn.le hm.le)
  have hp := mul_pos hn (Real.exp_pos (-(1/2 : ℝ)*Real.log (n/m)))
  nlinarith [Real.sqrt_nonneg (n*m)]

/-- The actual deleted survivor mean at a derived logarithmic time.
Only interior continuity and positivity are needed for this reservoir. -/
theorem interior_logarithmic_survivor_mean {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 1)) (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x) :
    ∃ c M : ℝ, 0 < c ∧ 0 < M ∧ M*c < 1/2 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 8 ≤ n → 16*r ≤ n →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ m : ℝ, 0 < m → m ≤ (n : ℝ) →
      Real.sqrt ((n : ℝ)*m)/16 ≤
        (n : ℝ)*deletedH (w n) removed (c*Real.log ((n : ℝ)/m)) := by
  obtain ⟨M, hM, hb⟩ := interior_deleted_survivor_reservoir hf hpos
  have hc : 0 < 1/(4*M) := by positivity
  have hMc : M*(1/(4*M)) = (1/4 : ℝ) := by field_simp
  refine ⟨1/(4*M), M, hc, hM, by rw [hMc]; norm_num, ?_⟩
  intro grid w hw n r hn hr removed hremoved m hm hmn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hl : 0 ≤ Real.log ((n : ℝ)/m) := Real.log_nonneg ((one_le_div hm).mpr hmn)
  have ht : 0 ≤ (1/(4*M))*Real.log ((n : ℝ)/m) := mul_nonneg hc.le hl
  have he : Real.exp (-(1/2 : ℝ)*Real.log ((n : ℝ)/m)) ≤
      Real.exp (-(M*((1/(4*M))*Real.log ((n : ℝ)/m)))) := by
    apply Real.exp_le_exp.mpr
    rw [← mul_assoc, hMc]
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left he (show 0 ≤ (n : ℝ)/16 by positivity)
  have hid := logarithmic_survival_sqrt_identity hnR hm
  have hlow : Real.sqrt ((n : ℝ)*m)/16 ≤
      ((n : ℝ)/16)*Real.exp (-(M*((1/(4*M))*Real.log ((n : ℝ)/m)))) := by
    nlinarith only [hscaled, hid]
  exact hlow.trans (hb grid w hw n r hn hr removed hremoved _ ht)

end Luce.Section6
