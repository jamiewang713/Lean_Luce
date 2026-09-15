import Luce.Section6NormalizedGapMoments
import Luce.Section6NormalizedGapTaylor
import Luce.Section6EventIntegral
import Luce.Section6InsertionProductBound

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

theorem deleted_kernel_product_square_integrable {n s : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin s → Fin n) (q : Fin s → ℕ) :
    Integrable (fun old => (∏ i, (deletedGapKernel w removed old (u i) (q i)).toReal)^2)
      (exponentialRace w) := by
  have hprod := deleted_kernel_product_integrable w removed u q
  apply (integrable_const (1 : ℝ)).mono' (hprod.aestronglyMeasurable.pow 2)
  filter_upwards [] with old
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb : (∏ i, (deletedGapKernel w removed old (u i) (q i)).toReal) ≤ 1 := by
    apply Finset.prod_le_one (fun i _ => ENNReal.toReal_nonneg)
    intro i _
    exact ENNReal.toReal_mono (by simp) (deletedGapKernel_le_one w removed old (u i) (q i))
  have h0 : 0 ≤ ∏ i, (deletedGapKernel w removed old (u i) (q i)).toReal :=
    Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  simpa only [Pi.pow_apply, one_pow] using pow_le_pow_left₀ h0 hb 2

/-- Integration of pointwise insertion errors on the original deleted
race. The gap moments and integrability are discharged here. Only the
deterministic event bounds and the actual-product second moment remain
as inputs to be supplied by the endpoint estimates. -/
theorem actual_normalized_product_error {n s : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (u : Fin s → Fin n)
    (q : Fin s ↪ Fin (Finset.univ \ removed).card)
    (K B eps b : Fin s → ℝ) (hK : ∀ i, 0 ≤ K i) (hB : ∀ i, 0 ≤ B i)
    (heps : ∀ i, 0 ≤ eps i) (hb : ∀ i, 0 ≤ b i)
    (hKB : ∀ i, K i ≤ B i) {G : Set (Fin n → ℝ)} (hG : MeasurableSet G)
    (hgood : ∀ᵐ old ∂exponentialRace w, old ∈ G → ∀ i,
      (deletedGapKernel w removed old (u i) (q i).val).toReal ≤
        B i*markedNormalizedGaps w removed q old i ∧
      |(deletedGapKernel w removed old (u i) (q i).val).toReal-
        K i*markedNormalizedGaps w removed q old i| ≤
        B i*(eps i*markedNormalizedGaps w removed q old i+
          b i*(markedNormalizedGaps w removed q old i)^2))
    {L : ℝ} (hL : 0 ≤ L)
    (hsecond : (∫ old, (∏ i, (deletedGapKernel w removed old (u i) (q i).val).toReal)^2
      ∂exponentialRace w) ≤ L^2) :
    |(∫ old, ∏ i, (deletedGapKernel w removed old (u i) (q i).val).toReal
        ∂exponentialRace w)-(∏ i, K i)| ≤
      (∏ i, B i)*(∑ i, (eps i+2*b i))+
        (L+(∏ i, K i)*Real.sqrt ((2 : ℝ)^s))*
          Real.sqrt ((exponentialRace w).real Gᶜ) := by
  let F := fun old => ∏ i, (deletedGapKernel w removed old (u i) (q i).val).toReal
  let Y := fun old => ∏ i, markedNormalizedGaps w removed q old i
  let E := fun old => (∏ i, B i)*
    ((∑ i, (eps i+b i*markedNormalizedGaps w removed q old i))*Y old)
  have hF : Integrable F (exponentialRace w) := deleted_kernel_product_integrable w removed u _
  have hF2 : Integrable (fun old => F old^2) (exponentialRace w) :=
    deleted_kernel_product_square_integrable w removed u _
  have hY : Integrable Y (exponentialRace w) := by
    simpa only [Y, pow_one] using integrable_markedNormalizedGaps_mixed w removed q (fun _ => 1)
  have hY2 : Integrable (fun old => Y old^2) (exponentialRace w) := by
    simpa only [Y, Finset.prod_pow] using integrable_markedNormalizedGaps_mixed w removed q (fun _ => 2)
  have hE : Integrable E (exponentialRace w) :=
    (integrable_marked_gap_weighted_error w removed q eps b).const_mul _
  have hF0 : ∀ᵐ old ∂exponentialRace w, 0 ≤ F old :=
    Filter.Eventually.of_forall (fun _ => Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg))
  have hY0 : ∀ᵐ old ∂exponentialRace w, 0 ≤ Y old :=
    (markedNormalizedGaps_nonneg_ae w removed q).mono
      (fun old hold => Finset.prod_nonneg (fun i _ => hold i))
  have hK0 : 0 ≤ ∏ i, K i := Finset.prod_nonneg (fun i _ => hK i)
  have hB0 : 0 ≤ ∏ i, B i := Finset.prod_nonneg (fun i _ => hB i)
  have hE0 : ∀ᵐ old ∂exponentialRace w, 0 ≤ E old := by
    filter_upwards [markedNormalizedGaps_nonneg_ae w removed q, hY0] with old hx hy
    exact mul_nonneg hB0 (mul_nonneg
      (Finset.sum_nonneg (fun i _ => add_nonneg (heps i) (mul_nonneg (hb i) (hx i)))) hy)
  have hpoint : ∀ᵐ old ∂exponentialRace w, old ∈ G → |F old-(∏ i, K i)*Y old| ≤ E old := by
    filter_upwards [markedNormalizedGaps_nonneg_ae w removed q, hgood] with old hx hg
    intro hold
    exact normalized_gap_product_comparison _ K B eps b _
      (fun _ => ENNReal.toReal_nonneg) hK hB heps hb hx
      (fun i => (hg hold i).1) hKB (fun i => (hg hold i).2)
  have hsplit := integral_comparison_good_bad hG hF (hY.const_mul (∏ i, K i)) hE hF0
    (hY0.mono (fun _ hy => mul_nonneg hK0 hy)) hE0 hpoint
  have hbadF : (∫ old in Gᶜ, F old ∂exponentialRace w) ≤
      L*Real.sqrt ((exponentialRace w).real Gᶜ) := by
    apply (setIntegral_le_second_moment hF hF2 hF0).trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_sqrt hsecond).trans_eq (Real.sqrt_sq hL)
  have hbadY := setIntegral_le_second_moment (A := Gᶜ) hY hY2 hY0
  rw [show (∫ old, Y old^2 ∂exponentialRace w) = (2 : ℝ)^s from
    integral_markedNormalizedGaps_prod_sq w removed q] at hbadY
  have hEY : (∫ old, Y old ∂exponentialRace w) = 1 := integral_markedNormalizedGaps_prod w removed q
  have hEE : (∫ old, E old ∂exponentialRace w) = (∏ i, B i)*(∑ i, (eps i+2*b i)) := by
    dsimp only [E, Y]
    rw [integral_const_mul, integral_marked_gap_weighted_error]
  rw [integral_const_mul, hEY, mul_one, hEE, integral_const_mul] at hsplit
  have hh := mul_le_mul_of_nonneg_left hbadY hK0
  dsimp only [F] at hsplit hbadF
  nlinarith only [hsplit, hbadF, hh]

end Luce.Section6
