import Luce.Section3CompensatorLimit
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Order.ProjIcc

/-!
# The literal interior intensity measure

The measure is Lebesgue measure restricted to (0,α], weighted by the
diagonal density from `eq:rho`. It is represented on the compact unit
interval for the Poisson-law construction. Mapping back to the real line
recovers the original density measure exactly.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace Luce

/-- The real-line intensity in Corollary 3.3. The exclusion of zero is
immaterial for Lebesgue measure and avoids assigning a profile value there. -/
def interiorDensityMeasure (f : ℝ → ℝ) (α : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (0 : ℝ) α)).withDensity (fun x => ENNReal.ofReal (profileDiagonal f x))

lemma profileDiagonal_nonneg {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) α) :
    0 ≤ profileDiagonal f x := by
  have hx1 : x < 1 := hx.2.trans_lt hα
  have hf0 : 0 ≤ f x := (hf.2.1 x ⟨hx.1, hx1⟩).le
  have hq : 0 ≤ profileQuantile profileMeasure f x :=
    profileQuantile_nonneg hf.integrable hf.ae_pos ⟨hx.1.le, hx1⟩
  exact div_nonneg (rateKernel_nonneg hf0) (profileD_pos hf.integrable hf.ae_pos hq).le

lemma integrable_profileDiagonal {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    Integrable (profileDiagonal f) (volume.restrict (Ioc (0 : ℝ) α)) := by
  simpa only [one_mul, IntegrableOn] using
    integrable_interior_density (g := fun _ => 1) hf hα continuousOn_const

lemma interiorDensityMeasure_finite {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    IsFiniteMeasure (interiorDensityMeasure f α) :=
  isFiniteMeasure_withDensity_ofReal (integrable_profileDiagonal hf hα).hasFiniteIntegral

/-- Compact-interval representation of the manuscript's intensity; the
finiteness proof is derived from Assumption 1.1. -/
def interiorIntensity (w : WeightArray) (f : ℝ → ℝ) (hf : ProfileLimit w f)
    (α : ℝ) (hα : α < 1) : FiniteMeasure (Icc (0 : ℝ) 1) :=
  FiniteMeasure.map (⟨interiorDensityMeasure f α, interiorDensityMeasure_finite hf hα⟩ : FiniteMeasure ℝ)
    (Set.projIcc (0 : ℝ) 1 zero_le_one)

lemma interiorDensityMeasure_ae_mem (f : ℝ → ℝ) (α : ℝ) :
    ∀ᵐ x ∂interiorDensityMeasure f α, x ∈ Ioc (0 : ℝ) α :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Ioc)

/-- Exact recovery of the real-line intensity. The projection changes no
point on the support of the density measure. -/
theorem interiorIntensity_projection_recovery (w : WeightArray) (f : ℝ → ℝ)
    (hf : ProfileLimit w f) (α : ℝ) (hα : α < 1) :
    (interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1)).map Subtype.val =
      interiorDensityMeasure f α := by
  change ((interiorDensityMeasure f α).map (Set.projIcc (0 : ℝ) 1 zero_le_one)).map
    Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe continuous_projIcc.measurable]
  calc
    _ = (interiorDensityMeasure f α).map id := by
      apply Measure.map_congr
      filter_upwards [interiorDensityMeasure_ae_mem f α] with x hx
      have hxx : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.trans hα.le⟩
      simp only [Function.comp_apply, Set.projIcc_of_mem zero_le_one hxx, id_eq]
    _ = _ := Measure.map_id

/-- Continuous spatial tests are genuinely integrable under the finite
intensity measure, independently of totalized integral conventions. -/
theorem integrable_interiorIntensity (w : WeightArray) (f : ℝ → ℝ)
    (hf : ProfileLimit w f) (α : ℝ) (hα : α < 1)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    Integrable g (interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1)) :=
  g.integrable _

/-- The continuous-test identity needed to apply Proposition 3.2 to the
actual intensity measure, with precisely the diagonal density. -/
theorem integral_interiorIntensity (w : WeightArray) (f : ℝ → ℝ)
    (hf : ProfileLimit w f) (α : ℝ) (hα : α < 1)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    (∫ y, g y ∂(interiorIntensity w f hf α hα : Measure (Icc (0 : ℝ) 1))) =
      ∫ x in Ioc (0 : ℝ) α,
        g (Set.projIcc (0 : ℝ) 1 zero_le_one x) * profileDiagonal f x := by
  change (∫ y, g y ∂(interiorDensityMeasure f α).map
    (Set.projIcc (0 : ℝ) 1 zero_le_one)) = _
  rw [integral_map continuous_projIcc.measurable.aemeasurable
    g.continuous.measurable.aestronglyMeasurable]
  unfold interiorDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (integrable_profileDiagonal hf hα).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [ENNReal.toReal_ofReal (profileDiagonal_nonneg hf hα hx), smul_eq_mul, mul_comm]

end Luce
