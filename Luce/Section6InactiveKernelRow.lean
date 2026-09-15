import Luce.Section6InactiveOrdinaryRow
import Luce.Section6StretchedExponentialSums

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- The complete inactive-right numerical kernel has a uniform row bound.
The stretched-exponential correction is summed by its proved series bound. -/
theorem inactive_terminal_kernel_row_bound {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n theta : ℝ), 1 ≤ n → 0 < theta →
    ∀ M : ℕ, 2*(M : ℝ) ≤ n →
    (∑ k ∈ Finset.range M, ((theta/((k : ℝ)+1))*
      (((k : ℝ)+1)/n)^(d*theta)+Real.exp (-d*Real.sqrt (n*((k : ℝ)+1))))) ≤ C := by
  obtain ⟨B, hB, hb⟩ := inactive_terminal_ordinary_row_bound hd
  have hs0 : Summable (fun k : ℕ => Real.exp (-d*Real.sqrt (k : ℝ))) := by
    simpa only [Real.rpow_zero, one_mul, ← Real.sqrt_eq_rpow] using
      summable_weighted_stretched_exp (b := 0) (by norm_num) hd (nu := 1/2) (by norm_num)
  have hs : Summable (fun k : ℕ => Real.exp (-d*Real.sqrt ((k : ℝ)+1))) := by
    have hh := hs0.comp_injective (i := fun k : ℕ => k+1) (fun a b hab => by
      dsimp only at hab
      omega)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hh
  let S := ∑' k : ℕ, Real.exp (-d*Real.sqrt ((k : ℝ)+1))
  refine ⟨B+max 1 S, by positivity, ?_⟩
  intro n theta hn ht M hMn
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hordinary := hb n theta hn0 ht M hMn
  have hrem : (∑ k ∈ Finset.range M, Real.exp (-d*Real.sqrt (n*((k : ℝ)+1)))) ≤ S := by
    calc
      _ ≤ ∑ k ∈ Finset.range M, Real.exp (-d*Real.sqrt ((k : ℝ)+1)) := by
        apply Finset.sum_le_sum
        intro k _
        apply Real.exp_le_exp.mpr
        have hh : (k : ℝ)+1 ≤ n*((k : ℝ)+1) := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
        have hr := Real.sqrt_le_sqrt hh
        nlinarith
      _ ≤ _ := hs.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)
  rw [Finset.sum_add_distrib]
  exact add_le_add hordinary (hrem.trans (le_max_right _ _))

end Luce.Section6
