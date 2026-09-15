import Luce.Section6FinitePopulationOrder
import Luce.Section6WeightedIntegrals

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- The exact second-moment estimate used in `lem:sp-quantiles`.
No moment assumption or endpoint hypothesis is needed for a finite row. -/
theorem populationD_two_le {n : ℕ} (w : Weights n) {t : ℝ} (ht : 0 < t) :
    populationD w 2 t ≤ (Real.exp (-1)/(t/2))*populationD w 1 (t/2) := by
  have hterm (i : Fin n) : w.rate i ^ 2 * survivalKernel t (w.rate i) ≤
      (Real.exp (-1)/(t/2))*(w.rate i * survivalKernel (t/2) (w.rate i)) := by
    have he : w.rate i ^ 2 * survivalKernel t (w.rate i) =
        rateKernel (t/2) (w.rate i)*rateKernel (t/2) (w.rate i) := by
      have hh := rateKernel_split_time t (w.rate i)
      dsimp only [rateKernel] at hh ⊢
      calc
        _ = w.rate i*(w.rate i*survivalKernel t (w.rate i)) := by ring
        _ = w.rate i*(w.rate i*survivalKernel (t/2) (w.rate i)*survivalKernel (t/2) (w.rate i)) := by rw [hh]
        _ = _ := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (rateKernel_le_exp_neg_one_div (half_pos ht))
      (rateKernel_nonneg (w.positive i).le)
  unfold populationD
  simp only [pow_one]
  calc
    _ ≤ (∑ i, (Real.exp (-1)/(t/2))*(w.rate i*survivalKernel (t/2) (w.rate i)))/(n : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hterm i) (Nat.cast_nonneg n)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- A finite population cannot change faster than its derivative at the
left endpoint of a positive time interval. -/
theorem populationD_one_difference_bound {n : ℕ} (w : Weights n) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) :
    |populationD w 1 t-populationD w 1 s| ≤
      ((Real.exp (-1)/(s/2))*populationD w 1 (s/2))*(t-s) := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc s t) :
      ‖-populationD w 2 x‖ ≤ (Real.exp (-1)/(s/2))*populationD w 1 (s/2) := by
    have hn : 0 ≤ populationD w 2 x := by
      unfold populationD
      apply div_nonneg _ (Nat.cast_nonneg n)
      exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (survivalKernel_pos _ _).le
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hn]
    exact (populationD_antitone w 2 hx.1).trans (populationD_two_le w hs)
  have hh := (convex_Icc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := populationD w 1) (f' := fun x => -populationD w 2 x)
    (fun x hx => (populationD_hasDerivAt w 1 x).hasDerivWithinAt) hd
    (show s ∈ Set.Icc s t from ⟨le_rfl, hst⟩)
    (show t ∈ Set.Icc s t from ⟨hst, le_rfl⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst)] using hh

end Luce.Section6
