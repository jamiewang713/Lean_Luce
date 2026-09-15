import Luce.Section7Definitions

/-! # Closed statement of Section 7's proposition

This statement spells out the density hypotheses without using a bundled
clock model and places the universal constant before every model input.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

namespace Luce.Section7
noncomputable section
universe u

def GeneralClockTailStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (n M : ℕ) (hM : 1 ≤ M) (hMn : M ≤ n)
      (g : Fin n → ℝ → ℝ)
      (_hgmeas : ∀ i, Measurable (g i)) (_hgnonneg : ∀ i t, 0 ≤ g i t)
      (_hgint : ∀ i, Integrable (g i)) (_hgmass : ∀ i, ∫ t, g i t = 1)
      (T : Fin n → Ω → ℝ)
      (_hLaw : ∀ i, HasLaw (T i) (volume.withDensity (fun t => ENNReal.ofReal (g i t))) P)
      (_hIndependent : iIndepFun T P)
      (B s : ℝ) (h : ℝ → ℝ)
      (_hBM : B - 1 ≥ 2 * (M : ℝ))
      (_hcut : (∑ i, P.real {ω | s < T i ω}) = B)
      (_hh : Integrable h)
      (_henv : ∀ m ∈ Finset.Icc 1 M, ∀ t ≥ s,
        g (terminalLabel n (lt_of_lt_of_le hM hMn) m) t ≤ h t),
      (∑ m ∈ Finset.Icc 1 M, P.real
        {ω | rankOf (fun i => T i ω) (terminalLabel n (lt_of_lt_of_le hM hMn) m) =
          (terminalLabel n (lt_of_lt_of_le hM hMn) m).val + 1}) ≤
        (M : ℝ) * Real.exp (-c * B) + 2 * ∫ t in Ioi s, h t

end
end Luce.Section7
