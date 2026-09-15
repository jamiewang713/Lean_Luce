import Luce.Section7Tail

/-! # The triangular-array consequence stated after Proposition 7.1 -/

open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter

namespace Luce.Section7
noncomputable section

/-- If the explicit right-hand side vanishes, so does the expected number
of terminal fixed points. Row lengths, laws, and probability spaces may vary. -/
theorem general_clock_tail_tendsto_zero
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (N M : ℕ → ℕ) (g : (k : ℕ) → Fin (N k) → ClockDensity)
    (T : (k : ℕ) → Fin (N k) → Ω k → ℝ)
    (hLaw : ∀ k i, HasLaw (T k i) (g k i).law (P k))
    (hIndependent : ∀ k, iIndepFun (T k) (P k))
    (hM : ∀ k, 1 ≤ M k) (hMN : ∀ k, M k ≤ N k)
    (B s : ℕ → ℝ) (h : ℕ → ℝ → ℝ)
    (hBM : ∀ k, 2 * (M k : ℝ) ≤ B k - 1)
    (hcut : ∀ k, (∑ i, (P k).real {ω | s k < T k i ω}) = B k)
    (hh : ∀ k, IntegrableOn (h k) (Ioi (s k)))
    (henv : ∀ k m, m ∈ Finset.Icc 1 (M k) → ∀ t ≥ s k,
      (g k (terminalLabel (N k) (lt_of_lt_of_le (hM k) (hMN k)) m)).density t ≤ h k t)
    (hvanish : Tendsto (fun k => (M k : ℝ) * Real.exp (-tailConstant * B k) +
      2 * ∫ t in Ioi (s k), h k t) atTop (𝓝 0)) :
    Tendsto (fun k => ∑ m ∈ Finset.Icc 1 (M k), (P k).real
      {ω | rankOf (fun i => T k i ω)
        (terminalLabel (N k) (lt_of_lt_of_le (hM k) (hMN k)) m) = N k - m + 1})
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun k =>
    Finset.sum_nonneg fun m _ => measureReal_nonneg) _ hvanish
  exact Eventually.of_forall fun k => general_clock_tail (P k) (g k) (T k)
    (hLaw k) (hIndependent k) (hM k) (hMN k) (h k) (hBM k) (hcut k) (hh k) (henv k)

end
end Luce.Section7
