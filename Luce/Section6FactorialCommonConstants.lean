import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem factorial_finite_positive_lower_bound {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) : ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ ∀ i, e ≤ a i := by
  let D := 1+∑ i, 1/a i
  have hD : 1 ≤ D := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) => (one_div_pos.mpr (ha i)).le)
    dsimp [D]; linarith
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  refine ⟨1/D, one_div_pos.mpr hD0, (one_div_le_one_div_of_le zero_lt_one hD).trans_eq (by norm_num), ?_⟩
  intro i
  have hi : 1/a i ≤ D := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j => 1/a j)
      (fun j _ => (one_div_pos.mpr (ha j)).le) (Finset.mem_univ i)
    dsimp [D]; linarith
  simpa only [one_div_one_div] using one_div_le_one_div_of_le (one_div_pos.mpr (ha i)) hi

theorem factorial_finite_common_upper_bound {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) : ∃ C : ℝ, 1 ≤ C ∧ ∀ i, a i ≤ C := by
  refine ⟨1+∑ i, a i, ?_, ?_⟩
  · have hh := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) => ha i)
    linarith
  · intro i
    have hh := Finset.single_le_sum (s := Finset.univ) (f := a) (fun j _ => ha j) (Finset.mem_univ i)
    linarith

end Luce.Section6
