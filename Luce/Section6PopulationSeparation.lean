import Luce.Section6FinitePopulationOrder

noncomputable section
open Set
namespace Luce.Section6

/-- Exact two-sided mean separation. Later quantile-scale bounds must
estimate these actual endpoint derivatives, not differentiate a remainder. -/
theorem populationG_separation {n : ℕ} (hn : 0 < n) (w : Weights n)
    {s t : ℝ} (hst : s ≤ t) :
    populationD w 1 t*(t-s) ≤ populationG w t-populationG w s ∧
    populationG w t-populationG w s ≤ populationD w 1 s*(t-s) := by
  have hd : Differentiable ℝ (populationG w) :=
    fun x => (populationG_hasDerivAt hn w x).differentiableAt
  have hderiv (x : ℝ) : deriv (populationG w) x = populationD w 1 x :=
    (populationG_hasDerivAt hn w x).deriv
  constructor
  · apply (convex_Icc s t).mul_sub_le_image_sub_of_le_deriv
      hd.continuous.continuousOn hd.differentiableOn _ s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
    intro x hx
    rw [hderiv]
    exact populationD_antitone w 1 (interior_subset hx).2
  · apply (convex_Icc s t).image_sub_le_mul_sub_of_deriv_le
      hd.continuous.continuousOn hd.differentiableOn _ s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
    intro x hx
    rw [hderiv]
    exact populationD_antitone w 1 (interior_subset hx).1

theorem populationH_separation {n : ℕ} (hn : 0 < n) (w : Weights n)
    {s t : ℝ} (hst : s ≤ t) :
    populationD w 1 t*(t-s) ≤ populationH w s-populationH w t ∧
    populationH w s-populationH w t ≤ populationD w 1 s*(t-s) := by
  have hh := populationG_separation hn w hst
  rw [populationG_eq_one_sub_H hn w, populationG_eq_one_sub_H hn w] at hh
  constructor <;> linarith [hh.1, hh.2]

end Luce.Section6
