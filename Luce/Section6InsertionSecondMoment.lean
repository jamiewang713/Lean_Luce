import Luce.Section6InsertionHolder
import Luce.Section6NormalizedProductError

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- Finite Hölder for the square of the actual insertion product. -/
theorem deleted_kernel_product_square_le_Lp {n s : ℕ} (w : Weights n) (hs : 0 < s)
    (removed : Finset (Fin n)) (u : Fin s → Fin n) (q : Fin s → ℕ) :
    (∫⁻ old, (∏ i, deletedGapKernel w removed old (u i) (q i))^2 ∂exponentialRace w) ≤
      (∏ i, eLpNorm (fun old => (deletedGapKernel w removed old (u i) (q i)).toReal)
        ((2*s : ℕ) : ℝ≥0∞) (exponentialRace w))^2 := by
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hsum : (∑ _i : Fin s, (s : ℝ)⁻¹) = 1 := by simp [hs.ne']
  have hholder := ENNReal.lintegral_prod_norm_pow_le (μ := exponentialRace w) Finset.univ
    (f := fun i : Fin s => fun old => (deletedGapKernel w removed old (u i) (q i))^(2*(s : ℝ)))
    (fun i _ => (measurable_deletedGapKernel w removed (u i) (q i)).aemeasurable.pow_const _)
    (p := fun _ => (s : ℝ)⁻¹) hsum (fun _ _ => inv_nonneg.mpr hsR.le)
  have hn (i : Fin s) (old : Fin n → ℝ) :
      ‖(deletedGapKernel w removed old (u i) (q i)).toReal‖ₑ =
        deletedGapKernel w removed old (u i) (q i) :=
    Real.enorm_toReal (ne_of_lt ((deletedGapKernel_le_one w removed old (u i) (q i)).trans_lt (by simp)))
  have hp0 : ((2*s : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.mul_pos (by omega) hs).ne'
  have hpinf : ((2*s : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have he : 2*(s : ℝ)*(s : ℝ)⁻¹ = 2 := by field_simp
  have hi : (1/(2*(s : ℝ)))*2 = (s : ℝ)⁻¹ := by field_simp
  simp_rw [← ENNReal.rpow_mul, he, ENNReal.rpow_two] at hholder
  rw [← Finset.prod_pow]
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpinf,
    ENNReal.toReal_natCast, Nat.cast_mul, Nat.cast_ofNat, hn,
    ← ENNReal.rpow_two, ← ENNReal.rpow_mul, hi]
  simpa only [Finset.prod_pow, ENNReal.rpow_two] using hholder

/-- Concrete one-factor Lp bounds imply the needed second moment;
dependence of the insertion factors is unrestricted. -/
theorem deleted_kernel_product_second_moment_bound {n s : ℕ} (w : Weights n) (hs : 0 < s)
    (removed : Finset (Fin n)) (u : Fin s → Fin n) (q : Fin s → ℕ)
    (B : Fin s → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hlp : ∀ i, eLpNorm (fun old => (deletedGapKernel w removed old (u i) (q i)).toReal)
      ((2*s : ℕ) : ℝ≥0∞) (exponentialRace w) ≤ ENNReal.ofReal (B i)) :
    (∫ old, (∏ i, (deletedGapKernel w removed old (u i) (q i)).toReal)^2
      ∂exponentialRace w) ≤ (∏ i, B i)^2 := by
  have hh := (deleted_kernel_product_square_le_Lp w hs removed u q).trans
    (pow_le_pow_left₀ (by positivity)
      (Finset.prod_le_prod (fun _ _ => zero_le) (fun i _ => hlp i)) 2)
  have hfinite : (∏ i, ENNReal.ofReal (B i))^2 ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top))
  have hreal := ENNReal.toReal_mono hfinite hh
  have hm : AEMeasurable (fun old => (∏ i, deletedGapKernel w removed old (u i) (q i))^2)
      (exponentialRace w) :=
    (Finset.measurable_prod _ (fun i _ => measurable_deletedGapKernel w removed (u i) (q i))).pow_const 2 |>.aemeasurable
  rw [← integral_toReal hm (by
    filter_upwards [] with old
    apply lt_of_le_of_lt (pow_le_pow_left₀ (by positivity)
      (Finset.prod_le_one (fun _ _ => zero_le)
        (fun i _ => deletedGapKernel_le_one w removed old (u i) (q i))) 2)
    norm_num)] at hreal
  simpa only [ENNReal.toReal_pow, ENNReal.toReal_prod, ENNReal.toReal_ofReal (hB _)] using hreal

end Luce.Section6
