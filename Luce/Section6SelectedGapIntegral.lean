import Luce.Section5GapMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

theorem unit_exponential_weighted_density (a : ℝ) :
    (fun x : ℝ => (exponentialPDF 1 x).toReal * Real.exp (-a*x)) =
      (Ici (0 : ℝ)).indicator (fun x => Real.exp (-(1+a)*x)) := by
  funext x
  rw [exponentialPDF_eq]
  by_cases hx : 0 ≤ x
  · rw [Set.indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx)]
    simp only [hx, if_true, one_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    ring
  · simp [hx]

/-- Exact Laplace transform under the actual rate-one exponential measure,
including integrability rather than relying on a totalized integral. -/
theorem unit_exponential_laplace {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun x : ℝ => Real.exp (-a*x)) (expMeasure 1) ∧
      (∫ x : ℝ, Real.exp (-a*x) ∂expMeasure 1) = 1/(1+a) := by
  have hm : Measurable (exponentialPDF 1) := (measurable_exponentialPDFReal 1).ennreal_ofReal
  have hneg : -(1+a) < 0 := by linarith
  constructor
  · change Integrable _ (volume.withDensity (exponentialPDF 1))
    rw [integrable_withDensity_iff_integrable_smul' hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul]
    rw [unit_exponential_weighted_density]
    apply (integrable_indicator_iff measurableSet_Ici).mpr
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (integrableOn_exp_mul_Ioi hneg 0)
  · change (∫ x : ℝ, Real.exp (-a*x) ∂volume.withDensity (exponentialPDF 1)) = _
    rw [integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul]
    rw [unit_exponential_weighted_density, integral_indicator measurableSet_Ici,
      integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi hneg 0]
    simp only [mul_zero, Real.exp_zero, div_neg, neg_div, neg_neg]

/-- Integrate a selected normalized spacing while retaining the survival
of later marked clocks, whose total rate is Lambda. -/
theorem selected_gap_integral {W theta Lambda : ℝ}
    (hW : 0 < W) (ht : 0 < theta) (hL : 0 ≤ Lambda) :
    Integrable (fun x : ℝ => (1-Real.exp (-theta*(x/W))) * Real.exp (-Lambda*(x/W)))
      (expMeasure 1) ∧
    (∫ x : ℝ, (1-Real.exp (-theta*(x/W))) * Real.exp (-Lambda*(x/W)) ∂expMeasure 1) =
      W*theta/((W+Lambda)*(W+Lambda+theta)) := by
  obtain ⟨hI, hInt⟩ := unit_exponential_laplace (div_nonneg hL hW.le)
  obtain ⟨hJ, hJnt⟩ := unit_exponential_laplace (div_nonneg (add_nonneg hL ht.le) hW.le)
  have he : (fun x : ℝ => (1-Real.exp (-theta*(x/W))) * Real.exp (-Lambda*(x/W))) =
      (fun x => Real.exp (-(Lambda/W)*x) - Real.exp (-((Lambda+theta)/W)*x)) := by
    funext x
    rw [sub_mul, one_mul, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [he]
  refine ⟨hI.sub hJ, ?_⟩
  rw [integral_sub hI hJ, hInt, hJnt]
  have hWL : W+Lambda ≠ 0 := ne_of_gt (by linarith)
  have hWLt : W+Lambda+theta ≠ 0 := ne_of_gt (by linarith)
  field_simp
  <;> ring

/-- Integrate any finite family of selected normalized spacings under the
explicit product law. The later-mark survival factors remain in every term. -/
theorem selected_gaps_product_integral {ι : Type*} [Fintype ι]
    (W theta Lambda : ι → ℝ) (hW : ∀ i, 0 < W i) (ht : ∀ i, 0 < theta i)
    (hL : ∀ i, 0 ≤ Lambda i) :
    Integrable (fun x : ι → ℝ => ∏ i,
      (1-Real.exp (-theta i*(x i/W i)))*Real.exp (-Lambda i*(x i/W i)))
      (Measure.pi fun _ : ι => expMeasure 1) ∧
    (∫ x : ι → ℝ, ∏ i, (1-Real.exp (-theta i*(x i/W i)))*Real.exp (-Lambda i*(x i/W i))
      ∂Measure.pi (fun _ : ι => expMeasure 1)) =
      ∏ i, W i*theta i/((W i+Lambda i)*(W i+Lambda i+theta i)) := by
  letI := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 1 by norm_num)
  constructor
  · exact Integrable.fintype_prod (fun i => (selected_gap_integral (hW i) (ht i) (hL i)).1)
  · rw [integral_fintype_prod_eq_prod (fun i x =>
      (1-Real.exp (-theta i*(x/W i)))*Real.exp (-Lambda i*(x/W i)))]
    exact Finset.prod_congr rfl fun i _ => (selected_gap_integral (hW i) (ht i) (hL i)).2

end Luce.Section6
