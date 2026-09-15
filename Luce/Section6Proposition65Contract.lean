import Luce.Section6LocalKernelDefinitions
import Luce.Section5GhostCylinder
import Luce.Section6Lemma64Contract

noncomputable section
open MeasureTheory ProbabilityTheory Function
namespace Luce.Section6.Proposition65Contract

/-- Closed target for the complete joint local insertion law. Every
configuration premise is a literal domain restriction in Proposition 6.5. -/
def localLaw : Prop :=
  ∀ (f : ℝ → ℝ) (left right : EndpointBehavior), PowerProfile f left right →
  ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
  ∀ r : ℕ, ∃ (h0 : ℕ) (delta v d kappa C : ℝ),
    1 ≤ h0 ∧ 0 < delta ∧ delta < 1 ∧ 0 < v ∧ v ≤ 1 ∧
    0 < d ∧ 0 < kappa ∧ 0 < C ∧
    (∀ (n s : ℕ), s ≤ r → ∀ (side : Fin s → Corner) (u j : Fin s → Fin n),
      Injective u → Injective j →
      (∀ e, (cornerBehavior left right (side e)).active) →
      (∀ e, h0 ≤ cornerDistance (side e) (u e) ∧ h0 ≤ cornerDistance (side e) (j e)) →
      (∀ e, (cornerDistance (side e) (u e) : ℝ) ≤ delta*(n : ℝ) ∧
        (cornerDistance (side e) (j e) : ℝ) ≤ delta*(n : ℝ)) →
      (∀ e, localCornerRatio (side e) (cornerBehavior left right (side e))
        (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e)) ≤
        (min (cornerDistance (side e) (u e) : ℝ) (cornerDistance (side e) (j e) : ℝ))^v) →
      (∀ e g, e ≠ g → 2*r < Nat.dist (j e).val (j g).val) →
      let err := |(exponentialRace (w n)).real {clocks | MarkedRankCylinder u j clocks} -
        ∏ e, localIdealKernel (side e) (cornerBehavior left right (side e))
          (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e))|
      let envelope := ∏ e, localEnvelopeKernel (side e) (cornerBehavior left right (side e)) d
        (cornerDistance (side e) (u e)) (cornerDistance (side e) (j e))
      err ≤ C*envelope*(∑ e,
        ((min (cornerDistance (side e) (u e) : ℝ) (cornerDistance (side e) (j e) : ℝ))^(-kappa) +
        ((max (cornerDistance (side e) (u e) : ℝ) (cornerDistance (side e) (j e) : ℝ))/(n : ℝ))^kappa)) ∧
      (∀ A B : ℝ, 0 < A →
        (∀ e, A ≤ (cornerDistance (side e) (u e) : ℝ) ∧
          A ≤ (cornerDistance (side e) (j e) : ℝ) ∧
          (cornerDistance (side e) (u e) : ℝ) ≤ B ∧
          (cornerDistance (side e) (j e) : ℝ) ≤ B) →
        err ≤ C*(A^(-kappa)+(B/(n : ℝ))^kappa)*envelope))

/-- Preserve the full global matrix properties for all other configurations,
including adjacent ranks; the second component is a conclusion, not an input. -/
def proposition65 : Prop := localLaw ∧ Lemma64Contract.matrix

end Luce.Section6.Proposition65Contract
