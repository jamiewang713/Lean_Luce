import Luce.Assumptions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Exact raw definitions for `ass:fixed-endpoint` in
`fixed_points_shell_condition.tex:253–280`. No analytic estimate is a field
of the assumption. Limits are taken in the extended nonnegative reals. -/

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace Luce

/-- Historical uniform condition, retained without changing its meaning. -/
abbrev UniformEndpointAssumption := EndpointAssumption

/-- Depth one is the last label; `k.val + 1` is its manuscript label. -/
def terminalDepth {n : ℕ} (k : Fin n) : ℕ := n - k.val

/-- Shell represented by its labels. The explicit `1 ≤ j` excludes shell zero. -/
def terminalShell (n j : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun k => 1 ≤ j ∧
    (j : ℝ) ≤ Real.log ((n : ℝ) / (terminalDepth k : ℝ)) ∧
    Real.log ((n : ℝ) / (terminalDepth k : ℝ)) < (j : ℝ) + 1

/-- The finite minimum exists only when the shell is nonempty. -/
def shellFloor (w : WeightArray) (n j : ℕ) (h : (terminalShell n j).Nonempty) : ℝ :=
  ((terminalShell n j).image (w n).rate).min' (h.image _)

/-- Empty shells contribute zero, not `exp 0`. -/
def shellCost (w : WeightArray) (n j : ℕ) : ℝ≥0∞ :=
  if h : (terminalShell n j).Nonempty then
    ENNReal.ofReal (Real.exp (-shellFloor w n j h * (j : ℝ))) else 0

/-- The literal sum over all nonempty shells of index at least `J`.
Finite support is proved separately, not presumed in the definition. -/
def shellTailCost (w : WeightArray) (n J : ℕ) : ℝ≥0∞ :=
  ∑' j : ℕ, if J ≤ j then shellCost w n j else 0

/-- The manuscript's iterated limit, with no uniform-in-row strengthening.
Normalization is deliberately separate. Row zero is empty and irrelevant. -/
def EndpointShellAssumption (w : WeightArray) : Prop :=
  Tendsto (fun J : ℕ => limsup (fun n : ℕ => shellTailCost w n J) atTop)
    atTop (𝓝 (0 : ℝ≥0∞))

end Luce
