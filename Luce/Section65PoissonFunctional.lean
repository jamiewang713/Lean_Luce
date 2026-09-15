import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

noncomputable section
open Polynomial
open scoped BigOperators
namespace Luce.Section6

/-- The falling factorial polynomials, as a basis of real polynomials. -/
def fallingSequence65 : Polynomial.Sequence ℝ where
  elems' := descPochhammer ℝ
  degree_eq' n := by
    rw [degree_eq_natDegree (monic_descPochhammer ℝ n).ne_zero,
      descPochhammer_natDegree]

def fallingBasis65 : Module.Basis ℕ ℝ ℝ[X] :=
  fallingSequence65.basis (fun n => by
    change IsUnit (descPochhammer ℝ n).leadingCoeff
    rw [(monic_descPochhammer ℝ n).leadingCoeff]
    exact isUnit_one)

@[simp] theorem fallingBasis65_apply (n : ℕ) :
    fallingBasis65 n = descPochhammer ℝ n := by
  simp [fallingBasis65, fallingSequence65]

/-- A polynomial functional specified by the factorial moments of a Poisson
law. This definition does not introduce any auxiliary random variables. -/
def poissonFunctional65 (μ : ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  fallingBasis65.constr ℝ (fun n => μ^n)

@[simp] theorem poissonFunctional65_desc (μ : ℝ) (n : ℕ) :
    poissonFunctional65 μ (descPochhammer ℝ n) = μ^n := by
  rw [← fallingBasis65_apply]
  exact fallingBasis65.constr_basis ℝ (fun n => μ^n) n

@[simp] theorem poissonFunctional65_one (μ : ℝ) :
    poissonFunctional65 μ 1 = 1 := by
  simpa using poissonFunctional65_desc μ 0

theorem descPochhammer_shift65 (n : ℕ) :
    (descPochhammer ℝ (n+1)).comp (X+1) =
      descPochhammer ℝ (n+1) + (n+1 : ℝ) • descPochhammer ℝ n := by
  have h := congrArg (fun p : ℝ[X] => p.comp (X+1))
    (descPochhammer_succ_comp_X_sub_one ℝ n)
  simp only [smul_eq_mul, sub_comp, mul_comp, add_comp, natCast_comp,
    one_comp, comp_assoc, X_comp] at h
  have hx : (X+1 : ℝ[X])-1 = X := by ring
  rw [hx] at h
  simp only [comp_X] at h
  rw [Algebra.smul_def, algebraMap_eq, map_add, map_natCast, map_one]
  linear_combination -h

theorem poissonFunctional65_stein (μ : ℝ) (p : ℝ[X]) :
    poissonFunctional65 μ (X*p) = μ * poissonFunctional65 μ (p.comp (X+1)) := by
  have hspan : p ∈ Submodule.span ℝ (Set.range (descPochhammer ℝ)) := by
    have h := fallingSequence65.span (fun n => by
      change IsUnit (descPochhammer ℝ n).leadingCoeff
      rw [(monic_descPochhammer ℝ n).leadingCoeff]
      exact isUnit_one)
    change p ∈ Submodule.span ℝ (Set.range fallingSequence65)
    rw [h]
    trivial
  induction hspan using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨n, rfl⟩ := hp
    have hx : X * descPochhammer ℝ n =
        descPochhammer ℝ (n+1) + (n : ℝ) • descPochhammer ℝ n := by
      rw [descPochhammer_succ_right, Algebra.smul_def, algebraMap_eq, map_natCast]
      ring
    rw [hx, map_add, map_smul, poissonFunctional65_desc, poissonFunctional65_desc]
    cases n with
    | zero => simp
    | succ n =>
      rw [descPochhammer_shift65, map_add, map_smul,
        poissonFunctional65_desc, poissonFunctional65_desc]
      simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
  | zero => simp
  | add p q hp hq ihp ihq =>
    simp only [mul_add, map_add, add_comp, ihp, ihq]
  | smul a p hp ih =>
    rw [mul_smul_comm, map_smul, smul_comp, map_smul, ih]
    simp only [smul_eq_mul]
    ring

end Luce.Section6
