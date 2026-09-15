import Luce.Section6JointGapMoment

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- The actual normalized insertion product is bounded by one on the
nonnegative spacing orthant, including repeated selected gaps. -/
theorem normalized_insertion_product_bounds {n : ℕ} {ι : Type*} [Fintype ι] (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (q : ι → Fin n) (theta : ι → ℝ)
    (ht : ∀ e, 0 ≤ theta e) (xi : Fin n → ℝ) (hx : ∀ l, 0 ≤ xi l) :
    0 ≤ (∏ e, exponentialGapMass (theta e) (gapStartFromNormalized w sigma (q e) xi)
      (xi (q e)/orderedRemainingRate w sigma (q e))) ∧
    (∏ e, exponentialGapMass (theta e) (gapStartFromNormalized w sigma (q e) xi)
      (xi (q e)/orderedRemainingRate w sigma (q e))) ≤ 1 := by
  have hb : ∀ e, 0 ≤ exponentialGapMass (theta e) (gapStartFromNormalized w sigma (q e) xi)
      (xi (q e)/orderedRemainingRate w sigma (q e)) ∧
      exponentialGapMass (theta e) (gapStartFromNormalized w sigma (q e) xi)
        (xi (q e)/orderedRemainingRate w sigma (q e)) ≤ 1 := by
    intro e
    refine ⟨exponentialGapMass_nonneg (ht e)
      (div_nonneg (hx _) (orderedRemainingRate_pos w sigma _).le), ?_⟩
    have hs := gapStartFromNormalized_nonneg w sigma (q e) (fun l _ => hx l)
    unfold exponentialGapMass survivalKernel
    have he : Real.exp (-gapStartFromNormalized w sigma (q e) xi * theta e) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (ht e))
    exact (sub_le_self _ (Real.exp_pos _).le).trans he
  exact ⟨Finset.prod_nonneg (fun e _ => (hb e).1),
    Finset.prod_le_one (fun e _ => (hb e).1) (fun e _ => (hb e).2)⟩

/-- Integrability needed for Fubini is derived from the actual product gap
law and positivity, rather than supplied as a local-law hypothesis. -/
theorem normalized_insertion_product_integrable {n : ℕ} {ι : Type*} [Fintype ι] (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (q : ι → Fin n) (theta : ι → ℝ)
    (ht : ∀ e, 0 ≤ theta e) :
    Integrable (fun xi => ∏ e, exponentialGapMass (theta e)
      (gapStartFromNormalized w sigma (q e) xi)
      (xi (q e)/orderedRemainingRate w sigma (q e))) (standardGapLaw n) := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  have hm : Continuous (fun xi => ∏ e, exponentialGapMass (theta e)
      (gapStartFromNormalized w sigma (q e) xi)
      (xi (q e)/orderedRemainingRate w sigma (q e))) := by
    unfold exponentialGapMass survivalKernel gapStartFromNormalized
    fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [standardGapLaw_nonneg_ae n] with xi hx
  have hb := normalized_insertion_product_bounds w sigma q theta ht xi hx
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

end Luce.Section6
