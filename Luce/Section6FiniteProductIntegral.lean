import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open MeasureTheory
namespace Luce.Section6

/-- Split Lebesgue measure on a finite tuple into its first coordinate and tail. -/
theorem integrable_fin_cons68 {k : ℕ} (f : (Fin (k+1) → ℝ) → ℝ) :
    Integrable f ↔ Integrable (fun z : ℝ × (Fin k → ℝ) => f (Fin.cons z.1 z.2))
      ((volume : Measure ℝ).prod volume) := by
  have hm := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (k+1) => (volume : Measure ℝ)) 0).symm
  simpa only [volume_pi, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq]
    using (hm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := f)).symm

theorem integral_fin_cons68 {k : ℕ} (f : (Fin (k+1) → ℝ) → ℝ)
    (hf : Integrable f) :
    (∫ y, f y) = ∫ s : ℝ, ∫ y : Fin k → ℝ, f (Fin.cons s y) := by
  have hm := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (k+1) => (volume : Measure ℝ)) 0).symm
  have he : (∫ y, f y) = ∫ z : ℝ × (Fin k → ℝ), f (Fin.cons z.1 z.2)
      ∂((volume : Measure ℝ).prod volume) := by
    simp only [volume_pi]
    rw [← hm.integral_comp']
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq]
  rw [he]
  exact integral_prod _ ((integrable_fin_cons68 f).mp hf)

end Luce.Section6
