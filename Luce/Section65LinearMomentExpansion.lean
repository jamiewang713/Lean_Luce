import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Luce.Section6

def linearCombination65 {ι : Type*} [Fintype ι] (t z : ι → ℝ) : ℝ := ∑ i, t i*z i

def multiplicity65 {ι : Type*} [DecidableEq ι] {k : ℕ} (v : Fin k → ι) (i : ι) : ℕ :=
  (Finset.univ.filter (fun j => v j = i)).card

theorem product_eq_multiplicity65 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (v : Fin k → ι) (z : ι → ℝ) :
    ∏ j : Fin k, z (v j) = ∏ i : ι, z i^(multiplicity65 v i) := by
  have h := Finset.prod_fiberwise_eq_prod_filter' (Finset.univ : Finset (Fin k))
    (Finset.univ : Finset ι) v z
  simpa [multiplicity65] using h.symm

theorem linearCombination65_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t z : ι → ℝ) (k : ℕ) :
    linearCombination65 t z ^ k = ∑ v : Fin k → ι,
      (∏ j : Fin k, t (v j)) * ∏ i : ι, z i^(multiplicity65 v i) := by
  rw [linearCombination65, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.prod_mul_distrib, product_eq_multiplicity65 v z]

end Luce.Section6
