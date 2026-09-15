import Luce.Section6Proposition610Contract
import Luce.Section6CoreFamilyQuantitative
import Luce.Section6CategoryCoreIdealSum

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace Luce.Section6

/-- Core factorial moments with the exact ideal category means. Every
probabilistic estimate is derived from the original sampled-profile model. -/
theorem proposition610 : Proposition610Contract.proposition610 := by
  classical
  intro f left right hp grid w hw q c hactive hc r
  let s := Fintype.card (CategoryCycleSlot r)
  let e : Fin s ≃ CategoryCycleSlot r := (Fintype.equivFin _).symm
  let side (a : Fin s) := (c (e a).1).side
  let k (a : Fin s) := (c (e a).1).lengthIndex
  obtain ⟨C, eta, hC, heta, N, hN, hbound⟩ :=
    hp.core_family_quantitative grid w hw side k (fun a => hactive (e a).1)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    (ideal_core_eventual_domain 1 (show (0 : ℝ) < 1 by norm_num))
  refine ⟨C, eta, hC, heta, s+1, max N N0, hN.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  obtain ⟨hn2, hA, _, hsep, _⟩ := hN0 n ((le_max_right _ _).trans hn)
  rw [core_category_expectation_eq_family_sum hn2 hsep c hc r e (w n),
    core_category_ideal_product_eq_family_sum hA (ideal_core_upper_le_population n) left right c r e,
    ← sub_div, abs_div]
  let D : ℝ := ∏ i, (((c i).lengthIndex+1 : ℕ) : ℝ)^r i
  have hD : 1 ≤ D := category_rotation_factor_ge_one c r
  rw [abs_of_nonneg (zero_le_one.trans hD)]
  exact (div_le_self (abs_nonneg _) hD).trans (hbound n hnN (categoryFamilyRestriction c r e))

end Luce.Section6
