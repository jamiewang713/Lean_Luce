import Luce.Section5CyclicAnalytic
import Luce.Section5Cycles
import Luce.Section4CountLaw
import Luce.Section4EndpointShellDefinitions

/-! Literal objects in the revised manuscript's short-cycle theorem.
These definitions supply no proof inputs or asymptotic restrictions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce

/-- Index k denotes cycles of length k+1. -/
def cycleTraceIntegrand (f : ℝ → ℝ) (k : ℕ) (x : Fin (k+1) → ℝ) : ℝ :=
  ∏ a, cyclicProfileDensity f (x a) (x (finRotate (k+1) a))

def cycleTraceIntensity (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (1 / (k+1 : ℝ)) * ∫ x, cycleTraceIntegrand f k x ∂cyclicProfileMeasure (k+1)

def cycleCountVector {n : ℕ} (L : ℕ) (R : Equiv.Perm (Fin n)) : Fin L → ℕ :=
  fun k => Section5.cycleCount R k.val

/-- The product measure means exactly independent Poisson coordinates.
Nonnegativity and finiteness of the raw intensities must be proved. -/
def cycleVectorPoissonLaw (f : ℝ → ℝ) (L : ℕ) : Measure (Fin L → ℕ) :=
  Measure.pi (fun k : Fin L => ProbabilityTheory.poissonMeasure (Real.toNNReal (cycleTraceIntensity f k.val)))

/-- The same sup-over-events convention as the scalar TV definition. -/
def cycleVectorTotalVariation {L : ℕ} (μ ν : Measure (Fin L → ℕ)) : ℝ :=
  sSup {r : ℝ | ∃ A : Set (Fin L → ℕ), r = |μ.real A - ν.real A|}

end Luce
