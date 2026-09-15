import Luce.Section6EnvelopeAbsorption
import Luce.Section6SlowPrototype

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem slow_survival_average_le (grid : SamplingGrid) {n : ℕ} (hn : 0 < n)
    {p r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    (∑ i : Fin n, Real.exp (-(r*(samplePoint grid n i)^p)))/(n : ℝ) ≤
      (1/r)^(1/p)*Real.Gamma (1+1/p) + 1/(n : ℝ) := by
  have hq := slow_survival_quadrature grid hn hp hr.le
  have hu := (abs_le.mp hq).2
  have hi := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_slow_survival hp hr) zero_le_one
  rw [integral_slow_survival hp hr] at hi
  have hn0 : 0 ≤ ∫ s in Ioi (1 : ℝ), Real.exp (-(r*s^p)) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  linarith

/-- Uniform sums of all nonnegative power envelopes at a right endpoint.
Both sampling grids are covered. The constant depends only on a and p,
not on n, r, or a rate-family regularity assumption. -/
theorem power_envelope_average_bound {a p : ℝ} (hp : 0 < p) (ha : 0 ≤ a/p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (grid : SamplingGrid) (n : ℕ), 0 < n → ∀ r : ℝ, 0 < r →
      (∑ i : Fin n, (samplePoint grid n i)^a * Real.exp (-(r*(samplePoint grid n i)^p)))/(n : ℝ) ≤
        C*(1/(r/2))^(a/p)*
          ((1/(r/2))^(1/p)*Real.Gamma (1+1/p) + 1/(n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := power_envelope_absorption hp.ne' ha
  refine ⟨C, hC, ?_⟩
  intro grid n hn r hr
  have hterm (i : Fin n) := hbound r (samplePoint grid n i) hr (samplePoint_mem grid i).1
  calc
    _ ≤ (∑ i : Fin n, C*(1/(r/2))^(a/p)*Real.exp (-((r/2)*(samplePoint grid n i)^p)))/(n : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hterm i) (Nat.cast_nonneg n)
    _ = (C*(1/(r/2))^(a/p))*
        ((∑ i : Fin n, Real.exp (-((r/2)*(samplePoint grid n i)^p)))/(n : ℝ)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (slow_survival_average_le grid hn hp (half_pos hr))
      (by positivity)

end Luce.Section6
