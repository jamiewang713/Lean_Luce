import Luce.Section2ProbabilityConvergence

/-! # Convergence in probability for triangular arrays

Rows may have different probability spaces. This matches the finite
exponential-clock model without imposing an artificial coupling of all rows.
-/

open MeasureTheory Filter
open scoped Topology

namespace Luce

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Convergence in probability to a real constant, allowing varying spaces. -/
def ConvergesInProbability (μ : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {ω | ε < |X n ω - c|}) atTop (𝓝 0)

namespace ConvergesInProbability

variable {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
  {X Y : ∀ n, Ω n → ℝ} {c d : ℝ}

theorem mono (hY : ConvergesInProbability μ Y d)
    (hbound : ∀ n ω, |X n ω - c| ≤ |Y n ω - d|) : ConvergesInProbability μ X c := by
  intro ε hε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (hY ε hε)
  intro n
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  exact hω.trans_le (hbound n ω)

/-- Changing variables on events whose probabilities vanish preserves the limit. -/
theorem congr_off (hY : ConvergesInProbability μ Y c) (bad : ∀ n, Set (Ω n))
    (hbad : Tendsto (fun n => (μ n).real (bad n)) atTop (𝓝 0))
    (heq : ∀ n ω, ω ∉ bad n → X n ω = Y n ω) : ConvergesInProbability μ X c := by
  intro ε hε
  have ht := (hY ε hε).add hbad
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa using ht)
  intro n
  calc
    (μ n).real {ω | ε < |X n ω - c|} ≤
        (μ n).real ({ω | ε < |Y n ω - c|} ∪ bad n) := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      by_cases hb : ω ∈ bad n
      · exact Or.inr hb
      · apply Or.inl
        change ε < |X n ω - c| at hω
        change ε < |Y n ω - c|
        rwa [heq n ω hb] at hω
    _ ≤ _ := measureReal_union_le _ _

theorem upper_tail (hX : ConvergesInProbability μ X c) {K : ℝ} (hK : c < K) :
    Tendsto (fun n => (μ n).real {ω | K < X n ω}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (hX (K - c) (sub_pos.mpr hK))
  intro n
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  have hsub : K - c < X n ω - c := sub_lt_sub_right hω c
  exact hsub.trans_le (le_abs_self _)

/-- Bounded convergence to the deterministic limit in `L¹`. -/
theorem integral_abs_tendsto (hX : ConvergesInProbability μ X c)
    (hXmeas : ∀ n, Measurable (X n)) {B : ℝ}
    (hbound : ∀ n ω, |X n ω - c| ≤ B) :
    Tendsto (fun n => ∫ ω, |X n ω - c| ∂μ n) atTop (𝓝 0) :=
  tendsto_integral_abs_of_bounded_probability μ X hXmeas hbound hX

end ConvergesInProbability
end Luce
