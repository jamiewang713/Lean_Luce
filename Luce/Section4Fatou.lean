import Luce.ConvergenceInProbability
import Mathlib.Topology.Order.LiminfLimsup

/-! # The expectation lower-semicontinuity step in Section 4

Source: `fixed_points.tex:936–945`. This version applies directly to the
nonnegative compensators already proved to converge in probability in
Section 3. Truncating at the deterministic limit avoids any assumed uniform
integrability or coupling of the row spaces.
-/

open MeasureTheory Filter
open scoped Topology

namespace Luce

/-- Nonnegative variables converging in probability to a constant have
expectation limsup at least that constant. Eventual boundedness is explicit
because a real-valued limsup is totalized for unbounded sequences. In the
Section 4 application it is supplied by the proved endpoint estimate. -/
theorem ConvergesInProbability.le_limsup_integral
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : ∀ n, Ω n → ℝ} {c : ℝ}
    (hX : ConvergesInProbability P X c)
    (hmeas : ∀ n, Measurable (X n)) (hint : ∀ n, Integrable (X n) (P n))
    (hpos : ∀ n ω, 0 ≤ X n ω) (hc : 0 ≤ c)
    (hbounded : IsBoundedUnder (· ≤ ·) atTop (fun n => ∫ ω, X n ω ∂P n)) :
    c ≤ limsup (fun n => ∫ ω, X n ω ∂P n) atTop := by
  let Y : ∀ n, Ω n → ℝ := fun n ω => min (X n ω) c
  have hYmeas (n : ℕ) : Measurable (Y n) := (hmeas n).min measurable_const
  have hYpos (n : ℕ) (ω : Ω n) : 0 ≤ Y n ω := le_min (hpos n ω) hc
  have hYle (n : ℕ) (ω : Ω n) : Y n ω ≤ c := min_le_right _ _
  have hY : ConvergesInProbability P Y c := by
    apply hX.mono
    intro n ω
    dsimp [Y]
    rcases le_total (X n ω) c with h | h
    · rw [min_eq_left h]
    · simp only [min_eq_right h, sub_self, abs_zero, abs_nonneg]
  have hYint (n : ℕ) : Integrable (Y n) (P n) := by
    apply Integrable.of_bound (hYmeas n).aestronglyMeasurable c
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hYpos n ω)]
      exact hYle n ω
  have habs := hY.integral_abs_tendsto hYmeas (B := c) (fun n ω => by
    rw [abs_of_nonpos (sub_nonpos.mpr (hYle n ω))]
    linarith [hYpos n ω])
  have hlim : Tendsto (fun n => ∫ ω, Y n ω ∂P n) atTop (𝓝 c) := by
    have herr : Tendsto (fun n => (∫ ω, Y n ω ∂P n) - c) atTop (𝓝 0) := by
      apply squeeze_zero_norm _ habs
      intro n
      have h := norm_integral_le_integral_norm (fun ω => Y n ω - c) (μ := P n)
      simpa [integral_sub (hYint n) (integrable_const c), Real.norm_eq_abs] using h
    simpa only [sub_add_cancel, zero_add] using herr.add_const c
  have hcomp : (fun n => ∫ ω, Y n ω ∂P n) ≤ᶠ[atTop]
      (fun n => ∫ ω, X n ω ∂P n) := Eventually.of_forall fun n =>
    integral_mono (hYint n) (hint n) (fun ω => min_le_left _ _)
  have h := limsup_le_limsup hcomp
    (isCoboundedUnder_le_of_le atTop (fun n => integral_nonneg (hYpos n))) hbounded
  rwa [hlim.limsup_eq] at h

end Luce
