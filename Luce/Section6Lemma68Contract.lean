import Luce.Section6IdealTraceDefinitions

/-! Closed targets for both assertions of manuscript Lemma 6.8.
The original profile is the only model input; convolution constants,
distinctness, canonical roots, core cutoffs and quantitative errors are literal. -/
noncomputable section
namespace Luce.Section6.Lemma68Contract

def total : Prop :=
  ∀ (f : ℝ → ℝ) (left right : EndpointBehavior), PowerProfile f left right →
  ∀ side : Corner, (cornerBehavior left right side).active →
  ∀ k : ℕ, ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
    ∃ M : ℕ, 1 ≤ M ∧ ∀ A B : ℕ, M ≤ A → A ≤ B →
      |idealTrace side (cornerBehavior left right side) k A B -
        cornerCoefficient side (cornerBehavior left right side) k * Real.log ((B : ℝ)/A)| ≤
      C₀ + C₁*((1+Real.log ((B : ℝ)/A))/(A : ℝ))

def spatial : Prop :=
  ∀ (f : ℝ → ℝ) (left right : EndpointBehavior), PowerProfile f left right →
  ∀ side : Corner, (cornerBehavior left right side).active →
  ∀ (k : ℕ) (a b : ℝ), 0 < a → a < b → b < 1 →
    ∃ C kappa : ℝ, 0 < C ∧ 0 < kappa ∧ ∃ K N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        |idealSpatialTrace side (cornerBehavior left right side) k n a b -
          cornerCoefficient side (cornerBehavior left right side) k * (b-a)*Real.log (n : ℝ)| ≤
        C*(1+Real.log (n : ℝ))^K*(idealCoreLower n : ℝ)^(-kappa)

def lemma68 : Prop := total ∧ spatial

end Luce.Section6.Lemma68Contract
