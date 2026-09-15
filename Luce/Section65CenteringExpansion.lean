import Luce.Section65RapidError
import Luce.Section65CenteredPoisson

noncomputable section
open Polynomial Filter
open scoped Topology BigOperators
namespace Luce.Section6

theorem LogGrowth65.neg {a : ℕ → ℝ} (ha : LogGrowth65 a) :
    LogGrowth65 (fun n => -a n) := by simpa [LogGrowth65] using ha

theorem LogGrowth65.prod {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ)
    (ha : ∀ i ∈ s, LogGrowth65 (a i)) : LogGrowth65 (fun n => ∏ i ∈ s, a i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using logGrowth65_const 1
  | @insert i s hi ih =>
    simpa [Finset.prod_insert hi] using
      (ha i (by simp)).mul (ih (fun j hj => ha j (by simp [hj])))

theorem centered_polynomial_expansion65 (μ : ℝ) (k : ℕ) :
    (X-C μ : ℝ[X])^k = ∑ j : Fin (k+1),
      ((k.choose j.val : ℝ)*(-μ)^(k-j.val)) • (X : ℝ[X])^j.val := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ((k.choose j : ℝ)*(-μ)^(k-j)) • (X : ℝ[X])^j) (k+1)]
  rw [sub_eq_add_neg, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_eq_C_mul]
  simp only [map_mul, map_natCast, map_pow, map_neg]
  ring

theorem centered_power_expansion65 (μ x : ℝ) (k : ℕ) :
    (x-μ)^k = ∑ j : Fin (k+1),
      ((k.choose j.val : ℝ)*(-μ)^(k-j.val)) * x^j.val := by
  have h := congrArg (fun p : ℝ[X] => p.eval x) (centered_polynomial_expansion65 μ k)
  simpa only [eval_pow, eval_sub, eval_X, eval_C, eval_finsetSum, eval_smul, smul_eq_mul] using h

theorem centeredPoissonMoment65_expansion (μ : ℝ) (k : ℕ) :
    centeredPoissonMoment65 μ k = ∑ j : Fin (k+1),
      ((k.choose j.val : ℝ)*(-μ)^(k-j.val)) * poissonFunctional65 μ ((X : ℝ[X])^j.val) := by
  have h := congrArg (poissonFunctional65 μ) (centered_polynomial_expansion65 μ k)
  simpa [centeredPoissonMoment65] using h

end Luce.Section6
