import Luce.Section1Assumptions
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas

/-! Literal hypotheses of fixed_points_sampled_profile.tex, Assumption
ass:simple-power-profile and thm:critical-pole. No population estimate,
normalization, shell condition, or probabilistic conclusion is an input. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

inductive SamplingGrid where
  | midpoint
  | interior
  deriving DecidableEq

def samplePoint (grid : SamplingGrid) (n : ℕ) (i : Fin n) : ℝ :=
  match grid with
  | .midpoint => ((i.val : ℝ) + 1 / 2) / (n : ℝ)
  | .interior => ((i.val : ℝ) + 1) / ((n : ℝ) + 1)

def SampledRates (grid : SamplingGrid) (w : WeightArray) (f : ℝ → ℝ) : Prop :=
  ∀ n (i : Fin n), (w n).rate i = f (samplePoint grid n i)

/-- `finite c` is an inactive endpoint with finite positive limit c.
`power c exponent eta` stores the leading coefficient, exponent, and error
exponent. All mathematical restrictions are in the predicates below. -/
inductive EndpointBehavior where
  | finite (c : ℝ)
  | power (c exponent eta : ℝ)

def EndpointBehavior.active : EndpointBehavior → Prop
  | .finite _ => False
  | .power _ _ _ => True

/-- Literal relative O(s^eta) expansion at zero from the right. -/
def PowerExpansion (g : ℝ → ℝ) (c exponent eta : ℝ) : Prop :=
  Asymptotics.IsBigO (𝓝[>] (0 : ℝ))
    (fun s => g s / (c * s ^ exponent) - 1) (fun s => s ^ eta)

def LeftBehavior (f : ℝ → ℝ) : EndpointBehavior → Prop
  | .finite c => 0 < c ∧ Tendsto f (𝓝[>] 0) (𝓝 c)
  | .power c alpha eta => 0 < c ∧ 1 < alpha ∧ 0 < eta ∧
      PowerExpansion f c (-alpha) eta

def RightBehavior (f : ℝ → ℝ) : EndpointBehavior → Prop
  | .finite c => 0 < c ∧ Tendsto (fun s => f (1-s)) (𝓝[>] 0) (𝓝 c)
  | .power c beta eta => 0 < c ∧ 0 < beta ∧ 0 < eta ∧
      PowerExpansion (fun s => f (1-s)) c beta eta

def PowerProfile (f : ℝ → ℝ) (left right : EndpointBehavior) : Prop :=
  ContinuousOn f (Ioo 0 1) ∧ (∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x) ∧
    LeftBehavior f left ∧ RightBehavior f right ∧ (left.active ∨ right.active)

/-- The critical regime is separate; no right power zero is permitted here. -/
def CriticalProfile (f : ℝ → ℝ) (c eta rightLimit : ℝ) : Prop :=
  ContinuousOn f (Ioo 0 1) ∧ (∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x) ∧
    0 < c ∧ 0 < eta ∧ PowerExpansion f c (-1) eta ∧
    0 < rightLimit ∧ Tendsto (fun s => f (1-s)) (𝓝[>] 0) (𝓝 rightLimit)

end Luce.Section6
