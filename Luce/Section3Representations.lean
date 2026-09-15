import Luce.Section3Poisson

/-! # Exact real-line and closed-interval representation identities

These identities make the correspondence with the literal notation in
`fixed_points.tex:737–743, 808–813` explicit in the kernel-checked interface.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Luce

/-- Deleting the zero endpoint does not change the manuscript intensity. -/
theorem interiorDensityMeasure_eq_closed (f : ℝ → ℝ) (α : ℝ) :
    interiorDensityMeasure f α =
      (volume.restrict (Icc (0 : ℝ) α)).withDensity
        (fun x => ENNReal.ofReal (profileDiagonal f x)) := by
  unfold interiorDensityMeasure
  rw [show volume.restrict (Ioc (0 : ℝ) α) = volume.restrict (Icc (0 : ℝ) α)
    from Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- The signed limiting integral agrees with the literal closed-interval
Lebesgue integral, including zero and empty intervals. -/
theorem interior_integral_eq_closed (f g : ℝ → ℝ) (α : ℝ) :
    (∫ x in Ioc (0 : ℝ) α, g x * profileDiagonal f x) =
      ∫ x in Icc (0 : ℝ) α, g x * profileDiagonal f x := by
  rw [show volume.restrict (Ioc (0 : ℝ) α) = volume.restrict (Icc (0 : ℝ) α)
    from Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- Forgetting the compact-interval subtype recovers exactly the paper's
real-line Dirac sum, with its one-based labels and inverse-rank convention. -/
theorem interiorFixedPoints_realMeasure {n : ℕ} (α : ℝ)
    (π : Equiv.Perm (Fin n)) :
    ((interiorFixedPoints α π).toFiniteMeasure : Measure (Icc (0 : ℝ) 1)).map
      Subtype.val = ∑ k : Fin n,
        if ((k.val : ℝ) + 1) / n ≤ α ∧ π.symm k = k then
          Measure.dirac (((k.val : ℝ) + 1) / n) else 0 := by
  classical
  rw [interiorFixedPoints_toFiniteMeasure, FiniteMeasure.toMeasure_sum,
    ← Measure.mapₗ_apply_of_measurable measurable_subtype_coe, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · change Measure.mapₗ Subtype.val (Measure.dirac (section3Location n k)) = _
    rw [Measure.mapₗ_apply_of_measurable measurable_subtype_coe,
      Measure.map_dirac' measurable_subtype_coe]
    rfl
  · simp

end Luce
