import Luce.Section6ContractDefinitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The concrete objects in Corollary 1.9 (`cor:sukhatme`) of
`fixed_points_sampled_profile.tex`. Labels and cycle lengths are zero based:
`i : Fin n` denotes label i+1, and k denotes cycles of length k+1. -/

noncomputable section
open MeasureTheory
open scoped Convolution
namespace Luce.Sukhatme

/-- The standard Sukhatme weights, n-i+1 in the manuscript's indexing. -/
def weights : WeightArray := fun n =>
  ⟨fun i => (n : ℝ) - i.val, fun i => sub_pos.mpr (by exact_mod_cast i.isLt)⟩

def density (w : ℝ) : ℝ := Real.exp w * Real.exp (-Real.exp w)

/-- k+1 convolution factors. -/
def convolution : ℕ → ℝ → ℝ
  | 0 => density
  | k+1 => density ⋆ convolution k

/-- The manuscript's b_(k+1). -/
def coefficient (k : ℕ) : ℝ := convolution k 0 / ((k : ℝ) + 1)

/-- The order-zero modified Bessel function on the positive real axis,
defined by its standard integral representation (DLMF 10.32.9, nu=0).
Only the positive argument 2 is used below. -/
def besselK0 (x : ℝ) : ℝ := ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * Real.cosh t)

def normalizedCycleVector {n : ℕ} (π : Equiv.Perm (Fin n)) (L : ℕ) : Fin L → ℝ :=
  fun k => ((Section5.cycleCount π k.val : ℝ) - coefficient k.val * Real.log n) /
    Real.sqrt (coefficient k.val * Real.log n)

def normalizedSpatialVector {n : ℕ} (π : Equiv.Perm (Fin n))
    (L J : ℕ) (a b : Fin J → ℝ) : (Fin L × Fin J) → ℝ :=
  fun z =>
    let mean := coefficient z.1.val * (b z.2 - a z.2) * Real.log n
    ((Section6.spatialCycleCount π .right z.1.val (a z.2) (b z.2) : ℝ) - mean) /
      Real.sqrt mean

end Luce.Sukhatme
