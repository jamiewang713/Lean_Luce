import Luce.Section65PoissonFunctional

noncomputable section
open Polynomial
open scoped BigOperators
namespace Luce.Section6

def centeredPoissonMoment65 (μ : ℝ) (k : ℕ) : ℝ :=
  poissonFunctional65 μ ((X-C μ)^k)

@[simp] theorem centeredPoissonMoment65_zero (μ : ℝ) :
    centeredPoissonMoment65 μ 0 = 1 := by
  simp [centeredPoissonMoment65]

theorem poissonFunctional65_centered_stein (μ : ℝ) (p : ℝ[X]) :
    poissonFunctional65 μ ((X-C μ)*p) =
      μ * poissonFunctional65 μ (p.comp (X+1)-p) := by
  have hs : C μ*p = μ • p := by simp [Algebra.smul_def]
  rw [sub_mul, map_sub, hs, map_smul, poissonFunctional65_stein, map_sub]
  simp only [smul_eq_mul]
  ring

theorem centeredPoissonMoment65_rec (μ : ℝ) (k : ℕ) :
    centeredPoissonMoment65 μ (k+1) =
      μ * ∑ j ∈ Finset.range k, (k.choose j : ℝ) * centeredPoissonMoment65 μ j := by
  have he : ((X-C μ)^k).comp (X+1)-(X-C μ)^k =
      ∑ j ∈ Finset.range k, (k.choose j : ℝ) • (X-C μ)^j := by
    rw [pow_comp, sub_comp, X_comp, C_comp]
    rw [show (X+1 : ℝ[X])-C μ = (X-C μ)+1 by ring, add_pow, Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
    rw [add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Algebra.smul_def, mul_comm]
  rw [centeredPoissonMoment65, pow_succ', poissonFunctional65_centered_stein,
    he, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [centeredPoissonMoment65]

@[simp] theorem centeredPoissonMoment65_one (μ : ℝ) :
    centeredPoissonMoment65 μ 1 = 0 := by
  simpa using centeredPoissonMoment65_rec μ 0

def scaledPoissonMoment65 (b : ℝ) (k : ℕ) : ℝ :=
  centeredPoissonMoment65 (b^2) k / b^k

@[simp] theorem scaledPoissonMoment65_zero (b : ℝ) :
    scaledPoissonMoment65 b 0 = 1 := by simp [scaledPoissonMoment65]

@[simp] theorem scaledPoissonMoment65_one (b : ℝ) :
    scaledPoissonMoment65 b 1 = 0 := by simp [scaledPoissonMoment65]

theorem scaledPoissonMoment65_rec (b : ℝ) (hb : b ≠ 0) (k : ℕ) :
    scaledPoissonMoment65 b (k+2) =
      ∑ j ∈ Finset.range (k+1), ((k+1).choose j : ℝ) *
        (b⁻¹)^(k-j) * scaledPoissonMoment65 b j := by
  unfold scaledPoissonMoment65
  rw [show k+2 = (k+1)+1 from rfl, centeredPoissonMoment65_rec,
    Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hp : b^((k+1)+1) = b^2 * (b^(k-j)*b^j) := by
    rw [← pow_add, Nat.sub_add_cancel hjk, ← pow_add]
    congr 1
    omega
  rw [hp, inv_pow]
  field_simp

end Luce.Section6
