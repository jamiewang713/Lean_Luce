import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Luce

/-- Nonnegative weights on a finite covered set can be charged to all
covering sets. Overlaps only enlarge the upper bound. -/
theorem finite_cover_sum_le {α ι : Type*} [Fintype α] [DecidableEq α]
    (S S₀ : Finset α) (I : Finset ι) (blocks : ι → Finset α) (F : α → ℝ)
    (hF : ∀ u, 0 ≤ F u)
    (hcover : ∀ u ∈ S, u ∈ S₀ ∨ ∃ r ∈ I, u ∈ blocks r) :
    (∑ u ∈ S, F u) ≤ (∑ u ∈ S₀, F u) + ∑ r ∈ I, ∑ u ∈ blocks r, F u := by
  classical
  have hpoint (u : α) : (if u ∈ S then F u else 0) ≤
      (if u ∈ S₀ then F u else 0) + ∑ r ∈ I, if u ∈ blocks r then F u else 0 := by
    have hsum : 0 ≤ ∑ r ∈ I, if u ∈ blocks r then F u else 0 :=
      Finset.sum_nonneg fun r _ => by split_ifs <;> first | exact hF u | exact le_refl 0
    by_cases hu : u ∈ S
    · rw [if_pos hu]
      rcases hcover u hu with hu₀ | ⟨r, hr, hur⟩
      · rw [if_pos hu₀]
        exact le_add_of_nonneg_right hsum
      · have hterm : F u ≤ ∑ r ∈ I, if u ∈ blocks r then F u else 0 := by
          simpa only [if_pos hur] using
            (Finset.single_le_sum (f := fun r => if u ∈ blocks r then F u else 0)
              (fun r _ => by split_ifs <;> first | exact hF u | exact le_refl 0) hr)
        exact hterm.trans (le_add_of_nonneg_left (by split_ifs <;> first | exact hF u | exact le_refl 0))
    · rw [if_neg hu]
      exact add_nonneg (by split_ifs <;> first | exact hF u | exact le_refl 0) hsum
  have h := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset α)) => hpoint u)
  simpa only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_add_distrib,
    Finset.sum_comm] using h

end Luce

