import Luce.Section7Contract
import Luce.Section7Tail

/-! # Independent check against the closed Section 7 statement -/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

namespace Luce.Section7
noncomputable section
universe u

/-- The full manuscript proposition, with its universal constant quantified
before the probability space, row size, densities, and cutoff parameters. -/
theorem proposition71 : GeneralClockTailStatement.{u} := by
  refine ⟨tailConstant, tailConstant_pos, ?_⟩
  intro Ω _ P _ n M hM hMn g hgmeas hgnonneg hgint hgmass
    T hLaw hIndependent B s h hBM hcut hh henv
  let densities : Fin n → ClockDensity := fun i =>
    ⟨g i, hgmeas i, hgnonneg i, hgint i, hgmass i⟩
  have hbound := general_clock_tail P densities T hLaw hIndependent hM hMn h
    hBM hcut hh.integrableOn henv
  convert hbound using 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [terminalLabel_val _ (Finset.mem_Icc.mp hm).1]

end
end Luce.Section7
