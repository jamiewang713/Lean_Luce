import Luce.Section65PoissonFunctional

noncomputable section
open Polynomial
open scoped BigOperators
namespace Luce.Section6

def fallingSupport65 (p : ℝ[X]) : Finset ℕ := (fallingBasis65.repr p).support

def fallingCoeff65 (p : ℝ[X]) (j : ℕ) : ℝ := fallingBasis65.repr p j

theorem polynomial_expansion65 (p : ℝ[X]) :
    p = ∑ j : ↥(fallingSupport65 p), fallingCoeff65 p j • descPochhammer ℝ j := by
  classical
  have h := fallingBasis65.linearCombination_repr p
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, fallingBasis65_apply,
    ] at h
  change p = ∑ j : ↥((fallingBasis65.repr p).support),
    (fallingBasis65.repr p) j.val • descPochhammer ℝ j.val
  rw [Finset.sum_coe_sort_eq_attach]
  exact h.symm.trans (Finset.sum_attach (fallingBasis65.repr p).support
    (fun j : ℕ => (fallingBasis65.repr p) j • descPochhammer ℝ j)).symm

theorem polynomial_eval_expansion65 (p : ℝ[X]) (x : ℝ) :
    p.eval x = ∑ j : ↥(fallingSupport65 p),
      fallingCoeff65 p j * (descPochhammer ℝ j).eval x := by
  have h := congrArg (fun q : ℝ[X] => q.eval x) (polynomial_expansion65 p)
  simpa only [eval_finsetSum, eval_smul, smul_eq_mul] using h

theorem poissonFunctional65_expansion (μ : ℝ) (p : ℝ[X]) :
    poissonFunctional65 μ p = ∑ j : ↥(fallingSupport65 p), fallingCoeff65 p j * μ^j.val := by
  have h := congrArg (poissonFunctional65 μ) (polynomial_expansion65 p)
  simpa using h

end Luce.Section6
