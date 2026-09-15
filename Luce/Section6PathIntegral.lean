import Luce.Section6TraceDensity

noncomputable section
open MeasureTheory Set
namespace Luce.Section6

/-- An open path with k intermediate vertices and k+1 density factors. -/
def openPathWeight68 (p : ℝ → ℝ) : (k : ℕ) → ℝ → ℝ → (Fin k → ℝ) → ℝ
  | 0, a, b, _ => p (a-b)
  | k+1, a, b, y => p (a-y 0)*openPathWeight68 p k (y 0) b (Fin.tail y)

theorem openPathWeight68_nonneg {p : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (k : ℕ) (a b : ℝ) (y : Fin k → ℝ) : 0 ≤ openPathWeight68 p k a b y := by
  induction k generalizing a b with
  | zero => exact hp _
  | succ k ih => exact mul_nonneg (hp _) (ih _ _ _)

theorem openPathWeight68_continuous {p : ℝ → ℝ} (hp : Continuous p) (k : ℕ) :
    Continuous (fun z : ℝ × ℝ × (Fin k → ℝ) => openPathWeight68 p k z.1 z.2.1 z.2.2) := by
  induction k with
  | zero => exact hp.comp (continuous_fst.sub (continuous_fst.comp continuous_snd))
  | succ k ih =>
    change Continuous (fun z : ℝ × ℝ × (Fin (k+1) → ℝ) =>
      p (z.1-z.2.2 0)*openPathWeight68 p k (z.2.2 0) z.2.1 (Fin.tail z.2.2))
    have ht : Continuous (fun z : ℝ × ℝ × (Fin (k+1) → ℝ) =>
        (z.2.2 0, z.2.1, Fin.tail z.2.2)) := by unfold Fin.tail; fun_prop
    exact (hp.comp (by fun_prop)).mul (ih.comp ht)

/-- Fubini identifies the literal path integral with the convolution, and
also proves the integrability required to use that identity. -/
theorem TraceDensity68.openPath_integral {p : ℝ → ℝ} (hp : TraceDensity68 p)
    (k : ℕ) (a b : ℝ) :
    Integrable (openPathWeight68 p k a b) ∧
      (∫ y : Fin k → ℝ, openPathWeight68 p k a b y) = traceConvolution68 p k (a-b) := by
  obtain ⟨M, hM0, hM⟩ := hp.bounded
  induction k generalizing a b with
  | zero => simp [openPathWeight68, traceConvolution68, measureReal_def, volume_pi, Measure.pi_empty_univ]
  | succ k ih =>
    have ht : Continuous (fun z : ℝ × (Fin k → ℝ) => (z.1, b, z.2)) := by fun_prop
    have hc : Continuous (fun z : ℝ × (Fin k → ℝ) =>
        p (a-z.1)*openPathWeight68 p k z.1 b z.2) :=
      (hp.continuous.comp (by fun_prop)).mul
        ((openPathWeight68_continuous hp.continuous k).comp ht)
    have hout : Integrable (fun s : ℝ => p (a-s)*traceConvolution68 p k (s-b)) := by
      apply ((hp.integrable.comp_sub_left a).mul_const M).mono'
        ((hp.continuous.comp (by fun_prop)).mul
          ((hp.convolution_continuous k).comp (by fun_prop))).aestronglyMeasurable
      filter_upwards [] with s
      change ‖p (a-s)*traceConvolution68 p k (s-b)‖ ≤ p (a-s)*M
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp.nonneg _) (hp.convolution_nonneg _ _))]
      exact mul_le_mul_of_nonneg_left (hp.convolution_bound hM k _) (hp.nonneg _)
    have hprod : Integrable (fun z : ℝ × (Fin k → ℝ) =>
        p (a-z.1)*openPathWeight68 p k z.1 b z.2)
        ((volume : Measure ℝ).prod volume) := by
      apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
      constructor
      · exact Filter.Eventually.of_forall (fun s => (ih s b).1.const_mul (p (a-s)))
      · have he (s : ℝ) :
            (∫ y : Fin k → ℝ, ‖p (a-s)*openPathWeight68 p k s b y‖) =
              p (a-s)*traceConvolution68 p k (s-b) := by
          simp_rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp.nonneg _)
            (openPathWeight68_nonneg hp.nonneg _ _ _ _))]
          rw [integral_const_mul, (ih s b).2]
        simpa only [he] using hout
    have hi : Integrable (openPathWeight68 p (k+1) a b) := by
      apply (integrable_fin_cons68 _).mpr
      simpa only [openPathWeight68, Fin.cons_zero, Fin.tail_cons] using hprod
    refine ⟨hi, ?_⟩
    rw [integral_fin_cons68 _ hi]
    simp only [openPathWeight68, Fin.cons_zero, Fin.tail_cons, integral_const_mul]
    simp_rw [(ih _ b).2]
    change (∫ s : ℝ, p (a-s)*traceConvolution68 p k (s-b)) =
      ∫ t : ℝ, p t*traceConvolution68 p k (a-b-t)
    rw [← integral_sub_left_eq_self
      (fun t : ℝ => p t*traceConvolution68 p k (a-b-t)) volume a]
    apply integral_congr_ae
    filter_upwards [] with s
    congr 2
    ring

end Luce.Section6
