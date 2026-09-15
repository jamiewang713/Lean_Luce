import Luce.Section6BernoulliCharacteristicEstimates

/-! Bounded complex exponential comparison on varying probability spaces. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Luce.BernoulliCLT

theorem integral_complex_difference_off
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Ω → ℂ} (hAi : Integrable A μ) (hBi : Integrable B μ)
    (hA : ∀ ω, ‖A ω‖ ≤ 1) (hB : ∀ ω, ‖B ω‖ ≤ 1)
    (bad : Set Ω) (hbad : MeasurableSet bad) (heq : ∀ ω, ω ∉ bad → A ω = B ω) :
    ‖(∫ ω, A ω ∂μ) - ∫ ω, B ω ∂μ‖ ≤ 2*μ.real bad := by
  rw [← integral_sub hAi hBi]
  calc
    _ ≤ ∫ ω, ‖A ω-B ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, bad.indicator (fun _ => (2 : ℝ)) ω ∂μ := by
      apply integral_mono (hAi.sub hBi).norm ((integrable_const 2).indicator hbad)
      intro ω
      change ‖A ω-B ω‖ ≤ bad.indicator (fun _ => (2 : ℝ)) ω
      by_cases hb : ω ∈ bad
      · rw [Set.indicator_of_mem hb]
        exact (norm_sub_le _ _).trans (by linarith [hA ω, hB ω])
      · rw [Set.indicator_of_notMem hb, heq ω hb, sub_self, norm_zero]
    _ = _ := by rw [integral_indicator hbad]; simp [mul_comm]

theorem integral_complex_product_error
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z F : Ω → ℂ} {c : ℂ} {C : ℝ}
    (hZ : Integrable Z μ) (hF : Integrable F μ)
    (hbound : ∀ ω, ‖Z ω‖ ≤ C) :
    ‖(∫ ω, Z ω * F ω ∂μ) - c * (∫ ω, Z ω ∂μ)‖ ≤
      C * ∫ ω, ‖F ω-c‖ ∂μ := by
  have hp : Integrable (fun ω => Z ω * F ω) μ :=
    hF.bdd_mul hZ.aestronglyMeasurable (ae_of_all μ hbound)
  have hd := hp.sub (hZ.const_mul c)
  rw [← integral_const_mul, ← integral_sub hp (hZ.const_mul c)]
  calc
    _ ≤ ∫ ω, ‖Z ω * F ω - c * Z ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, C * ‖F ω-c‖ ∂μ := by
      apply integral_mono hd.norm ((hF.sub (integrable_const c)).norm.const_mul C)
      intro ω
      change ‖Z ω * F ω-c*Z ω‖ ≤ C*‖F ω-c‖
      rw [show Z ω * F ω - c * Z ω = Z ω * (F ω-c) by ring, norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound ω) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem integral_exp_difference_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {f g : ∀ n, Ω n → ℂ} {R : ∀ n, Ω n → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : ∀ n, Measurable (g n))
    (hfre : ∀ n ω, (f n ω).re ≤ 0) (hgre : ∀ n ω, (g n ω).re ≤ 0)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ n ω, ‖f n ω - g n ω‖ ≤ C * |R n ω|)
    (hR : ConvergesInProbability μ R 0) :
    Tendsto (fun n => ∫ ω, ‖Complex.exp (f n ω) - Complex.exp (g n ω)‖ ∂μ n)
      atTop (𝓝 0) := by
  let E : ∀ n, Ω n → ℝ := fun n ω => ‖Complex.exp (f n ω) - Complex.exp (g n ω)‖
  have hE : ConvergesInProbability μ E 0 := by
    intro ε hε
    let δ := min (1/C) (ε/(2*C))
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    apply squeeze_zero (fun _ => measureReal_nonneg) _ (hR δ hδ)
    intro n
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    simp only [Set.mem_ofPred_eq, sub_zero] at hω ⊢
    by_contra hh
    have hr : |R n ω| ≤ δ := le_of_not_gt hh
    have h1 : C * |R n ω| ≤ 1 := calc
      _ ≤ C * (1/C) := mul_le_mul_of_nonneg_left (hr.trans (min_le_left _ _)) hC.le
      _ = 1 := by field_simp
    have h2 : 2 * (C * |R n ω|) ≤ ε := calc
      _ ≤ 2 * (C * (ε/(2*C))) := by gcongr; exact hr.trans (min_le_right _ _)
      _ = ε := by field_simp
    have hnorm := exp_difference_le (hgre n ω) ((hbound n ω).trans h1)
    have hle : E n ω ≤ ε := hnorm.trans ((mul_le_mul_of_nonneg_left
      (hbound n ω) (by norm_num)).trans h2)
    exact (not_lt_of_ge hle) (by simpa [E] using hω)
  have hemeas (n : ℕ) : Measurable (E n) :=
    ((Complex.measurable_exp.comp (hf n)).sub (Complex.measurable_exp.comp (hg n))).norm
  have heBound (n : ℕ) (ω : Ω n) : |E n ω - 0| ≤ 2 := by
    simp only [E, sub_zero, abs_of_nonneg (norm_nonneg _)]
    have h1 := norm_exp_le_one (hfre n ω)
    have h2 := norm_exp_le_one (hgre n ω)
    exact (norm_sub_le _ _).trans (by linarith)
  simpa [E] using hE.integral_abs_tendsto hemeas heBound

end Luce.BernoulliCLT
