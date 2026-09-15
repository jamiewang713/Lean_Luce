import Luce.Section6GapCoordinates
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Luce.Section6

theorem exponentialPDF_toReal_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun t => (exponentialPDF a t).toReal) volume := by
  apply integrable_toReal_of_lintegral_ne_top
    ((measurable_exponentialPDFReal a).ennreal_ofReal).aemeasurable
  change (∫⁻ t, exponentialPDF a t) ≠ ⊤
  rw [lintegral_exponentialPDF_eq_one ha]
  exact ENNReal.one_ne_top

/-- The joint finite exponential law has the literal product density.
The proof establishes integrability rather than totalizing divergent integrals. -/
theorem finite_exponential_product_density {ι : Type*} [Fintype ι]
    (rate : ι → ℝ) (hpos : ∀ i, 0 < rate i) :
    Measure.pi (fun i => expMeasure (rate i)) =
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))).withDensity
        (fun x => ∏ i, exponentialPDF (rate i) (x i)) := by
  classical
  letI : ∀ i, IsProbabilityMeasure (expMeasure (rate i)) := fun i =>
    isProbabilityMeasure_expMeasure (hpos i)
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  let f := fun i t => (exponentialPDF (rate i) t).toReal
  have hf (i : ι) : Integrable (f i) (volume.restrict (s i)) :=
    (exponentialPDF_toReal_integrable (hpos i)).restrict
  have hprod (x : ι → ℝ) : ENNReal.ofReal (∏ i, f i (x i)) =
      ∏ i, exponentialPDF (rate i) (x i) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
    apply Finset.prod_congr rfl
    intro i _
    exact ENNReal.ofReal_toReal (by simp [exponentialPDF])
  simp_rw [← hprod]
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hf)
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => ENNReal.toReal_nonneg))),
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => ENNReal.toReal_nonneg))]
  apply Finset.prod_congr rfl
  intro i _
  rw [ofReal_integral_eq_lintegral_ofReal (hf i)
    (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
  simp_rw [show (fun t => ENNReal.ofReal (f i t)) = exponentialPDF (rate i) by
    funext t; exact ENNReal.ofReal_toReal (by simp [exponentialPDF])]
  change (∫⁻ t in s i, exponentialPDF (rate i) t) =
    (volume.withDensity (exponentialPDF (rate i))) (s i)
  exact (withDensity_apply _ (hs i)).symm

/-- Ordered gap masses as nonnegative product-density integrals on exactly
the assigned marked coordinates. The count-gap region includes terminal gaps. -/
theorem gapOrderedKernel_eq_simplex_lintegral {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (k : ℕ) (hu : Function.Injective u)
    (old : Fin n → ℝ) :
    gapOrderedKernel w u q k old =
      ∫⁻ t in gapSimplexRegion u q k old,
        ∏ a : GapCoordinates q k, exponentialPDF (w.rate (u a.val)) (t a)
        ∂Measure.pi (fun _ : GapCoordinates q k => (volume : Measure ℝ)) := by
  rw [gapOrderedKernel_eq_simplex_measure w u q k hu old,
    finite_exponential_product_density (fun a : GapCoordinates q k => w.rate (u a.val))
      (fun a => w.positive (u a.val)),
    withDensity_apply _ (measurableSet_gapSimplexRegion u q k old)]

end Luce.Section6
