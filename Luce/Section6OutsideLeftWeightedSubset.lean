import Luce.Section6OutsideLeftWeightedSum

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Arbitrary subsets of the early half obey the same weighted kernel bound. -/
theorem outside_left_weighted_subset_bound {n : ℕ} {theta alpha kappa d : ℝ}
    (hn : 0 < n) (htheta : 0 ≤ theta) (hk : kappa < alpha) (hd : 0 ≤ d)
    (s : Finset (Fin n)) (hs : ∀ j ∈ s, 2*(j.val+1) ≤ n) :
    (∑ j ∈ s,
      ((n : ℝ)/((j.val : ℝ)+1))^kappa*
        (theta*(((j.val : ℝ)+1)/(n : ℝ))^alpha/((j.val : ℝ)+1))*
        Real.exp (-d*(theta*(((j.val : ℝ)+1)/(n : ℝ))^alpha))) ≤
      theta*(1/(alpha-kappa)+2*(1/2 : ℝ)^(alpha-kappa)) := by
  classical
  let g : ℕ → ℝ := fun k => ((n : ℝ)/((k : ℝ)+1))^kappa*
    (theta*(((k : ℝ)+1)/(n : ℝ))^alpha/((k : ℝ)+1))*
    Real.exp (-d*(theta*(((k : ℝ)+1)/(n : ℝ))^alpha))
  let T := s.image Fin.val
  have he : (∑ j ∈ s, g j.val) = ∑ k ∈ T, g k := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Fin.ext hab
  have hsub : T ⊆ Finset.range (n/2) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hh := hs j hj
    apply Finset.mem_range.mpr
    omega
  have hdom : (∑ k ∈ T, g k) ≤ ∑ k ∈ Finset.range (n/2), g k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by dsimp [g]; positivity)
  have hhalf : 2*((n/2 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (show 2*(n/2) ≤ n by omega)
  change (∑ j ∈ s, g j.val) ≤ _
  rw [he]
  exact hdom.trans (outside_left_weighted_sum_bound (Nat.cast_pos.mpr hn) htheta hk hd (n/2) hhalf)

end Luce.Section6
