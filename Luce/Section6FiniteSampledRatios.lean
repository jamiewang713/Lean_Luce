import Luce.Section6Sampling
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Finitely many sampled rows admit the rate-dependent absorption
constant. It is constructed from the two grids, not assumed of the model. -/
theorem finite_sampled_rate_ratio_bound (f : ℝ → ℝ) (alpha : ℝ) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ), n ≤ M → ∀ i : Fin n,
      1 ≤ C*((w n).rate i/(n : ℝ)^alpha) := by
  classical
  let I := (a : Fin (M+1)) × Fin a.val
  let q : SamplingGrid → I → ℝ := fun grid a =>
    (a.1.val : ℝ)^alpha / f (samplePoint grid a.1.val a.2)
  let F : I → ℝ := fun a => |q .midpoint a| + |q .interior a|
  let C : ℝ := 1 + ∑ a : I, F a
  have hF (a : I) : 0 ≤ F a := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro grid w hw n hn i
  let a : I := ⟨⟨n, by omega⟩, i⟩
  have hq : q grid a ≤ C := by
    have hs : F a ≤ ∑ b : I, F b := Finset.single_le_sum (fun b _ => hF b) (Finset.mem_univ a)
    have ha : |q grid a| ≤ F a := by
      cases grid <;> dsimp [F] <;> linarith [abs_nonneg (q .midpoint a), abs_nonneg (q .interior a)]
    exact (le_abs_self _).trans (ha.trans (hs.trans (by dsimp [C]; linarith)))
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hr := (w n).positive i
  have hq' : (n : ℝ)^alpha/(w n).rate i ≤ C := by
    simpa only [q, a, ← hw n i] using hq
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hn0 alpha)).mpr
  simpa only [one_mul] using (div_le_iff₀ hr).mp hq'

end Luce.Section6
