import Luce.Section6ProfileDefinitions
import Luce.Section5MaximumRoot
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.ContinuousMap.Bounded.Basic

noncomputable section
open MeasureTheory
open scoped BigOperators Convolution
namespace Luce.Section6

inductive Corner where
  | left
  | right
  deriving DecidableEq

instance : Fintype Corner where
  elems := {.left, .right}
  complete x := by cases x <;> simp

def cornerBehavior (left right : EndpointBehavior) : Corner → EndpointBehavior
  | .left => left
  | .right => right

def incrementDensity (gamma q w : ℝ) : ℝ :=
  gamma * q * Real.exp (gamma*w) * Real.exp (-q*Real.exp (gamma*w))

/-- Index k represents k+1 convolution factors, including k=0. -/
def convolutionDensity (gamma q : ℝ) : ℕ → ℝ → ℝ
  | 0 => incrementDensity gamma q
  | k+1 => incrementDensity gamma q ⋆ convolutionDensity gamma q k

def cornerCoefficient (side : Corner) (behavior : EndpointBehavior) (k : ℕ) : ℝ :=
  match behavior with
  | .finite _ => 0
  | .power _ gamma _ =>
    let q := match side with
      | .right => (Real.Gamma (1+1/gamma)) ^ gamma
      | .left => (Real.Gamma (1-1/gamma)) ^ (-gamma)
    convolutionDensity gamma q k 0 / ((k : ℝ)+1)

def totalCoefficient (left right : EndpointBehavior) (k : ℕ) : ℝ :=
  cornerCoefficient .left left k + cornerCoefficient .right right k

def cornerDistance (side : Corner) {n : ℕ} (i : Fin n) : ℕ :=
  match side with
  | .left => i.val+1
  | .right => n-i.val

def logLocation (side : Corner) {n : ℕ} (i : Fin n) : ℝ :=
  Real.log (cornerDistance side i) / Real.log n

/-- Actual cycles modulo rotation, rooted at their largest label. -/
def spatialCycleCount {n : ℕ} (R : Equiv.Perm (Fin n)) (side : Corner)
    (k : ℕ) (a b : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun c : ↥(Section5.cycleOrbits R k) =>
    a < logLocation side (Section5.cycleMaximum R k c) ∧
      logLocation side (Section5.cycleMaximum R k c) ≤ b).card

/-- Count cycles having a vertex farther than delta*log n from their root
in logarithmic endpoint distance. This is the stated localization event. -/
def excursionCycleCount {n : ℕ} (R : Equiv.Perm (Fin n)) (side : Corner)
    (k : ℕ) (a b delta : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun c : ↥(Section5.cycleOrbits R k) =>
    a < logLocation side (Section5.cycleMaximum R k c) ∧
    logLocation side (Section5.cycleMaximum R k c) ≤ b ∧
    ∃ v ∈ c.val.toFinset,
      |Real.log (cornerDistance side v) -
        Real.log (cornerDistance side (Section5.cycleMaximum R k c))| >
          delta * Real.log n).card

def standardNormalVector (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)

def normalizedCycleVector {n : ℕ} (R : Equiv.Perm (Fin n))
    (left right : EndpointBehavior) (L : ℕ) : Fin L → ℝ :=
  fun k => ((Section5.cycleCount R k.val : ℝ) - totalCoefficient left right k.val * Real.log n) /
    Real.sqrt (totalCoefficient left right k.val * Real.log n)

abbrev SpatialIndex (left right : EndpointBehavior) (L J : ℕ) :=
  {side : Corner // (cornerBehavior left right side).active} × Fin L × Fin J

instance (left right : EndpointBehavior) (L J : ℕ) :
    Fintype (SpatialIndex left right L J) := by
  classical
  unfold SpatialIndex
  infer_instance

def normalizedSpatialVector {n : ℕ} (R : Equiv.Perm (Fin n))
    (left right : EndpointBehavior) (L J : ℕ) (a b : Fin J → ℝ) :
    SpatialIndex left right L J → ℝ :=
  fun z =>
    let c := cornerCoefficient z.1.val (cornerBehavior left right z.1.val) z.2.1.val
    let mean := c * (b z.2.2 - a z.2.2) * Real.log n
    ((spatialCycleCount R z.1.val z.2.1.val (a z.2.2) (b z.2.2) : ℝ) - mean) /
      Real.sqrt mean

end Luce.Section6
