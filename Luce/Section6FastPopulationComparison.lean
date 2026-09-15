import Luce.Section6FastEnvelopeSums
import Luce.Section6FastProfileComparison

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem populationG_eq_samples (grid : SamplingGrid) (w : WeightArray)
    (f : ℝ → ℝ) (hw : SampledRates grid w f) (n : ℕ) (t : ℝ) :
    populationG (w n) t =
      (∑ i : Fin n, (1-survivalKernel t (f (samplePoint grid n i))))/(n : ℝ) := by
  unfold populationG
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hw n i]

/-- The actual arrival population compared with the fast-power prototype.
The selected exponent and the envelope sum are proved from the profile. -/
theorem PowerProfile.left_populationG_comparison {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (h : PowerProfile f (.power c alpha eta) right) :
    ∃ eta' : ℝ, 0 < eta' ∧ eta' < eta ∧ eta' < alpha-1 ∧
    ∃ K : ℝ, 0 < K ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t → t ≤ 1 →
    |populationG (w n) t -
      (∑ i : Fin n, (1-Real.exp (-((c*t)*(samplePoint grid n i)^(-alpha)))))/(n : ℝ)| ≤
      K*(t^(1/(alpha-eta'))+1/(n : ℝ)) := by
  have hc := h.2.2.1.1
  have ha := h.2.2.1.2.1
  obtain ⟨eta', he, heeta, healpha, C, M, hC, hM, hdiff⟩ := h.left_arrival_difference_bound
  obtain ⟨E, hE, hsum⟩ := fast_power_envelope_average_bound ha he healpha (half_pos hc)
  have hq : 1 < alpha-eta' := by linarith
  have hq0 : 0 < alpha-eta' := zero_lt_one.trans hq
  refine ⟨eta', he, heeta, healpha, C*E+M, by positivity, ?_⟩
  intro grid w hw n hn t ht ht1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let s : Fin n → ℝ := samplePoint grid n
  let env : Fin n → ℝ := fun i => (s i)^(-alpha+eta')*
    Real.exp (-(((c/2)*t)*(s i)^(-alpha)))
  have hterm (i : Fin n) :
      |(1-survivalKernel t (f (s i))) - (1-Real.exp (-((c*t)*(s i)^(-alpha))))| ≤
      C*t*env i + t*M := by
    have hh := hdiff (s i) (samplePoint_mem grid i) t ht.le
    have h1 : -t*(c*(s i)^(-alpha)) = -((c*t)*(s i)^(-alpha)) := by ring
    have h2 : -t*((c/2)*(s i)^(-alpha)) = -(((c/2)*t)*(s i)^(-alpha)) := by ring
    simpa only [env, survivalKernel, h1, h2, mul_assoc] using hh
  have hbound : |populationG (w n) t -
      (∑ i : Fin n, (1-Real.exp (-((c*t)*(s i)^(-alpha)))))/(n : ℝ)| ≤
      C*(t*((∑ i, env i)/(n : ℝ)))+t*M := by
    rw [populationG_eq_samples grid w f hw n t, ← sub_div, abs_div, abs_of_pos hn0]
    calc
      _ ≤ (∑ i : Fin n,
          |(1-survivalKernel t (f (s i)))-(1-Real.exp (-((c*t)*(s i)^(-alpha))))|)/(n : ℝ) := by
        apply div_le_div_of_nonneg_right _ hn0.le
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (∑ i : Fin n, (C*t*env i+t*M))/(n : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hterm i) hn0.le
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_div]
        field_simp
  have he' := hsum grid n hn t ht ht1
  change t*((∑ i, env i)/(n : ℝ)) ≤ E*(t^(1/(alpha-eta'))+1/(n : ℝ)) at he'
  have hsmall : t ≤ t^(1/(alpha-eta')) := by
    have hle : 1/(alpha-eta') ≤ (1 : ℝ) := (div_le_one hq0).mpr hq.le
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 hle
  calc
    _ ≤ C*(t*((∑ i, env i)/(n : ℝ)))+t*M := hbound
    _ ≤ C*(E*(t^(1/(alpha-eta'))+1/(n : ℝ)))+M*t^(1/(alpha-eta')) :=
      add_le_add (mul_le_mul_of_nonneg_left he' hC.le)
        (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsmall hM.le)
    _ ≤ _ := by
      have hh := mul_nonneg hM.le (one_div_nonneg.mpr hn0.le)
      nlinarith

end Luce.Section6
