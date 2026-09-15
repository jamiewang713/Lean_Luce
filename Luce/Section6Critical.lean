import Luce.Section6CriticalFixedPoints
import Luce.Section6CriticalLongerCycles
import Luce.Section6Contract

/-! Section 6.6: the critical pole. The proof establishes the fixed-point
normal limit, its mean asymptotic, and bounded means for every longer cycle,
for both sampling grids and arbitrary probability spaces with the Luce law. -/

noncomputable section
open MeasureTheory
universe u
namespace Luce.Section6

/-- The complete critical-profile theorem, checked against the independent
closed manuscript contract. All analytic and probabilistic estimates are
derived from the original critical profile and exact sampling assumptions. -/
theorem critical (grid : SamplingGrid) : SampledProfileContract.critical.{u} grid := by
  intro Ω mΩ P hP
  letI : ∀ n, MeasurableSpace (Ω n) := mΩ
  letI : ∀ n, IsProbabilityMeasure (P n) := hP
  intro w f c eta d hw hp π hπ hMass
  obtain ⟨hclt,hmean⟩ := hp.fixed_point_limits P grid w hw π hπ hMass
  refine ⟨hclt,hmean,?_⟩
  intro k
  obtain ⟨C,_,hbound⟩ := hp.longer_cycle_race_bound (k+1) (by omega)
  refine ⟨C,fun n => ?_⟩
  rw [luce_cycle_statistic_integral_eq (P n) (w n) (π n) (hπ n) (hMass n) (k+1)
    (fun x => (x : ℝ))]
  exact hbound grid w hw n

end Luce.Section6
