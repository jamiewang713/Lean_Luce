import Luce.Section6LocalErrorPowers

noncomputable section
namespace Luce.Section6

theorem finite_positive_lower_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ f i := by
  classical
  let s : Finset ι := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  refine ⟨s.inf' hs f, (Finset.lt_inf'_iff hs).mpr (fun i _ => hf i), ?_⟩
  intro i
  exact Finset.inf'_le f (Finset.mem_univ i)

theorem finite_nonneg_le_one_add_sum {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (i : ι) : f i ≤ 1+∑ j, f j := by
  have hh := Finset.single_le_sum (s := Finset.univ) (fun j _ => hf j) (Finset.mem_univ i)
  linarith only [hh]

end Luce.Section6
