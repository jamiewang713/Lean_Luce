import Luce.Section5GapExpectation
import Luce.Section5GapTaylor

/-!
# Products of the microscopic gap coefficients

Source: `fixed_points.tex:1035–1048`. Uniform scalar errors are converted
to product errors with explicit bounds. The expectation transfer still
uses the actual second moment of the selected normalized gaps.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Luce
set_option backward.isDefEq.respectTransparency false

lemma abs_prod_le_uniform {r : ℕ} {A : Fin r → ℝ} {C : ℝ}
    (hA : ∀ a, |A a| ≤ C) : |∏ a, A a| ≤ C ^ r := by
  rw [Finset.abs_prod]
  simpa using Finset.prod_le_prod (s := Finset.univ)
    (fun a _ => abs_nonneg (A a)) (fun a _ => hA a)

/-- A concrete modulus for finite products, valid at C=0 and r=0. -/
lemma product_error_modulus {r : ℕ} {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    {A B : Fin r → ℝ} (hA : ∀ a, |A a| ≤ C) (hB : ∀ a, |B a| ≤ C)
    (hAB : ∀ a, |A a - B a| < ε / (((r : ℝ) + 1) * (C + 1) ^ r)) :
    |(∏ a, A a) - ∏ a, B a| < ε := by
  let δ := ε / (((r : ℝ) + 1) * (C + 1) ^ r)
  have hCp : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hε (mul_pos (by positivity) (pow_pos hCp r))
  have he := abs_prod_sub_prod_le_relative Finset.univ A B (fun _ => C + 1) (fun _ => δ)
    (fun a _ => (hA a).trans (by linarith))
    (fun a _ => (hB a).trans (by linarith))
    (fun _ _ => hCp.le) (fun _ _ => hδ.le)
    (fun a _ => (hAB a).le.trans (by dsimp [δ]; nlinarith [hδ.le]))
  simp only [Finset.sum_const, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at he
  have heq : (((r : ℝ) + 1) * δ) * (C + 1) ^ r = ε := by
    dsimp [δ]
    field_simp
  have hp := mul_pos hδ (pow_pos hCp r)
  nlinarith

/-- Uniform convergence of scalar coefficients in probability gives
uniform convergence of their product in probability. The target values
may vary with both the row and the marked configuration. -/
theorem uniform_product_error_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    {ι : ℕ → Type*} {r : ℕ}
    (A : (n : ℕ) → ι n → Ω n → Fin r → ℝ)
    (B : (n : ℕ) → ι n → Fin r → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ i, ∀ᵐ x ∂μ n,
      (∀ a, |A n i x a| ≤ C) ∧ (∀ a, |B n i a| ≤ C))
    (hprob : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, ∀ i,
        (μ n).real {x | ∃ a, δ ≤ |A n i x a - B n i a|} < η) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, ∀ i,
        (μ n).real {x | ε ≤ |(∏ a, A n i x a) - ∏ a, B n i a|} < η := by
  intro ε hε η hη
  let δ := ε / (((r : ℝ) + 1) * (C + 1) ^ r)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [hbound, hprob δ hδ η hη] with n hn hp i
  apply lt_of_le_of_lt _ (hp i)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hn i] with x hx
  intro herr
  by_contra hnexist
  have hgood : ∀ a, |A n i x a - B n i a| < δ :=
    fun a => lt_of_not_ge fun ha => hnexist ⟨a, ha⟩
  exact not_le_of_gt (product_error_modulus hC hε hx.1 hx.2 hgood) herr

end Luce
