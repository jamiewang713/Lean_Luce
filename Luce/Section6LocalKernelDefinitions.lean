import Luce.Section6ContractDefinitions

noncomputable section
namespace Luce.Section6

/-- The exact coefficient q_sigma in the manuscript. The inactive value
is unused by the local law, which requires every marked corner active. -/
def localCornerQ (side : Corner) (behavior : EndpointBehavior) : ℝ :=
  match behavior with
  | .finite _ => 0
  | .power _ gamma _ => match side with
    | .right => (Real.Gamma (1+1/gamma))^gamma
    | .left => (Real.Gamma (1-1/gamma))^(-gamma)

def localCornerExponent (behavior : EndpointBehavior) : ℝ :=
  match behavior with
  | .finite _ => 0
  | .power _ gamma _ => gamma

/-- x_R=(a/h)^beta and x_L=(h/a)^alpha, with real division. -/
def localCornerRatio (side : Corner) (behavior : EndpointBehavior) (a h : ℕ) : ℝ :=
  match side with
  | .right => ((a : ℝ)/(h : ℝ))^(localCornerExponent behavior)
  | .left => ((h : ℝ)/(a : ℝ))^(localCornerExponent behavior)

/-- Literal ideal kernel K_sigma, with the physical target-depth denominator. -/
def localIdealKernel (side : Corner) (behavior : EndpointBehavior) (a h : ℕ) : ℝ :=
  localCornerExponent behavior * localCornerQ side behavior * localCornerRatio side behavior a h /
    (h : ℝ) * Real.exp (-localCornerQ side behavior * localCornerRatio side behavior a h)

/-- Literal slack envelope H_sigma; d is a constructed positive constant. -/
def localEnvelopeKernel (side : Corner) (behavior : EndpointBehavior) (d : ℝ) (a h : ℕ) : ℝ :=
  localCornerRatio side behavior a h / (h : ℝ) *
    Real.exp (-d * localCornerRatio side behavior a h)

end Luce.Section6
