import Luce.Section6ExponentialProductDensity

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Literal product of marked exponential densities on the ordered gap region. -/
def gapSimplexIntegral {n r : ℕ} (w : Weights n) (u : Fin r → Fin n)
    (q : Fin r → ℕ) (k : ℕ) (old : Fin n → ℝ) : ℝ :=
  ∫ t in gapSimplexRegion u q k old,
    ∏ a : GapCoordinates q k, w.rate (u a.val)*Real.exp (-(w.rate (u a.val)*t a))
    ∂Measure.pi (fun _ : GapCoordinates q k => (volume : Measure ℝ))

theorem gapSimplexIntegral_integrable_and_eq {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (k : ℕ) (hu : Injective u)
    (old : Fin n → ℝ) :
    IntegrableOn (fun t => ∏ a : GapCoordinates q k,
      w.rate (u a.val)*Real.exp (-(w.rate (u a.val)*t a))) (gapSimplexRegion u q k old)
      (Measure.pi (fun _ : GapCoordinates q k => (volume : Measure ℝ))) ∧
    (gapOrderedKernel w u q k old).toReal = gapSimplexIntegral w u q k old := by
  let μ := Measure.pi (fun _ : GapCoordinates q k => (volume : Measure ℝ))
  let S := gapSimplexRegion u q k old
  let g := fun t : GapCoordinates q k → ℝ => ∏ a, exponentialPDF (w.rate (u a.val)) (t a)
  have hm : Measurable g := Finset.measurable_prod _ (fun a _ =>
    ((measurable_exponentialPDFReal (w.rate (u a.val))).ennreal_ofReal).comp (measurable_pi_apply a))
  have hfinite : (∫⁻ t in S, g t ∂μ) ≠ ⊤ := by
    rw [← gapOrderedKernel_eq_simplex_lintegral w u q k hu old]
    exact ne_of_lt ((gapOrderedKernel_le_one w u q k old).trans_lt (by simp))
  have heq : (fun t => (g t).toReal) =ᵐ[μ.restrict S]
      (fun t => ∏ a : GapCoordinates q k, w.rate (u a.val)*Real.exp (-(w.rate (u a.val)*t a))) := by
    filter_upwards [ae_restrict_mem (measurableSet_gapSimplexRegion u q k old)] with t ht
    dsimp only [g]
    rw [ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro a _
    rw [exponentialPDF_of_nonneg ((ht.1 a).1.le),
      ENNReal.toReal_ofReal (mul_nonneg (w.positive _).le (Real.exp_pos _).le)]
  refine ⟨(integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfinite).congr heq, ?_⟩
  rw [gapOrderedKernel_eq_simplex_lintegral w u q k hu old]
  change (∫⁻ t in S, g t ∂μ).toReal = _
  calc
    _ = ∫ t in S, (g t).toReal ∂μ := by
      symm
      apply integral_toReal hm.aemeasurable
      exact Filter.Eventually.of_forall (fun t => ENNReal.prod_lt_top
        (fun a _ => by simp [exponentialPDF]))
    _ = _ := integral_congr_ae heq

/-- The exact real cylinder identity with literal ordered density integrals.
The gap regions currently use the exact count-gap representation. -/
theorem markedRankCylinder_real_probability_eq_simplex_product {n r : ℕ}
    (w : Weights n) (u j : Fin r → Fin n) (hu : Injective u) (hj : Injective j) :
    (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} =
      ∫ old, ∏ k ∈ Finset.univ.image (sortedMarkedGapIndex j),
        gapSimplexIntegral w (u ∘ Tuple.sort j) (sortedMarkedGapIndex j) k old
        ∂exponentialRace w := by
  rw [markedRankCylinder_real_probability_eq_gap_product w u j hu hj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun old => Finset.prod_congr rfl fun k _ =>
    (gapSimplexIntegral_integrable_and_eq w _ _ k (hu.comp (Tuple.sort j).injective) old).2

theorem gapSimplexProduct_integrable {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (hu : Injective u) :
    Integrable (fun old => ∏ k ∈ Finset.univ.image q, gapSimplexIntegral w u q k old)
      (exponentialRace w) := by
  apply (gapOrderedProduct_integrable w u q).congr
  exact Filter.Eventually.of_forall fun old => Finset.prod_congr rfl fun k _ =>
    (gapSimplexIntegral_integrable_and_eq w u q k hu old).2

end Luce.Section6
