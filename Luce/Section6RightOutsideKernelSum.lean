import Luce.Section6SampledWeightedSubsets
import Luce.Section6StretchedExponentialSums

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Uniform row sum of the outside-right ordinary kernel plus its
row-size stretched-exponential remainder. No source-rate bound is assumed. -/
theorem right_outside_kernel_subset_bound {beta d nu : ℝ}
    (hb : 0 < beta) (hd : 0 < d) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (theta : ℝ), 0 < n → 0 < theta →
    ∀ s : Finset (Fin n),
    (∑ j ∈ s, ((theta*((n : ℝ)/(terminalDepth j : ℝ))^beta/(terminalDepth j : ℝ))*
      Real.exp (-(d*(theta*((n : ℝ)/(terminalDepth j : ℝ))^beta)))+
      Real.exp (-d*(n : ℝ)^nu))) ≤ C := by
  obtain ⟨B, hB, hbrow⟩ := inverse_power_kernel_row_bound hb hd
  have hseries : Summable (fun n : ℕ => (n : ℝ)*Real.exp (-d*(n : ℝ)^nu)) := by
    simpa only [Real.rpow_one] using summable_weighted_stretched_exp (b := 1) zero_le_one hd hnu
  let D : ℝ := max 1 (∑' n : ℕ, (n : ℝ)*Real.exp (-d*(n : ℝ)^nu))
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨B+D, add_pos hB hD, ?_⟩
  intro n theta hn ht s
  let F : ℕ → ℝ := fun h => (theta*((n : ℝ)/(h : ℝ))^beta/(h : ℝ))*
    Real.exp (-(d*(theta*((n : ℝ)/(h : ℝ))^beta)))+Real.exp (-d*(n : ℝ)^nu)
  have hinj : Function.Injective (terminalDepth : Fin n → ℕ) := by
    intro a b hab
    apply Fin.ext
    unfold terminalDepth at hab
    have ha := a.isLt
    have hb := b.isLt
    omega
  have hfinite := positive_depth_subset_sum_le s terminalDepth hinj
    (fun j => ⟨terminalDepth_pos j, Nat.sub_le _ _⟩) F (fun h hh => by dsimp [F]; positivity)
  have hrem : (n : ℝ)*Real.exp (-d*(n : ℝ)^nu) ≤ D :=
    (hseries.le_tsum n (fun k _ => by positivity)).trans (le_max_right _ _)
  apply hfinite.trans
  have ho := hbrow (n : ℝ) theta (Nat.cast_pos.mpr hn) ht n
  simpa only [F, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
    Nat.add_sub_cancel, nsmul_eq_mul] using add_le_add ho hrem

end Luce.Section6
