import Luce.Section2ConvergenceInProbability

/-! # Elementary limit assembly for the Section 3 proof -/

open MeasureTheory Filter Set
open scoped Topology

namespace Luce.ConvergesInProbability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {X Y : ∀ n, Ω n → ℝ} {c d : ℝ}

theorem deterministic {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 c)) :
    ConvergesInProbability μ (fun n _ => a n) c := by
  intro ε hε
  have hevent : ∀ᶠ n in atTop, |a n - c| < ε := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp ha) ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [hevent] with n hn
  have hs : {ω : Ω n | ε < |a n - c|} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_lt_of_ge hn.le
  simp [hs]

theorem add (hX : ConvergesInProbability μ X c) (hY : ConvergesInProbability μ Y d) :
    ConvergesInProbability μ (fun n ω => X n ω + Y n ω) (c + d) := by
  intro ε hε
  have hlim := (hX (ε / 2) (half_pos hε)).add (hY (ε / 2) (half_pos hε))
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa using hlim)
  intro n
  calc
    _ ≤ (μ n).real ({ω | ε / 2 < |X n ω - c|} ∪ {ω | ε / 2 < |Y n ω - d|}) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      by_contra h
      have h' := not_or.mp h
      have hx := le_of_not_gt (show ¬ ε / 2 < |X n ω - c| from h'.1)
      have hy := le_of_not_gt (show ¬ ε / 2 < |Y n ω - d| from h'.2)
      have heq : X n ω + Y n ω - (c + d) = (X n ω - c) + (Y n ω - d) := by ring
      have hb := abs_add_le (X n ω - c) (Y n ω - d)
      rw [← heq] at hb
      change ε < |X n ω + Y n ω - (c + d)| at hω
      linarith
    _ ≤ _ := measureReal_union_le _ _

theorem neg (hX : ConvergesInProbability μ X c) :
    ConvergesInProbability μ (fun n ω => -X n ω) (-c) := by
  apply hX.mono
  intro n ω
  have heq : -X n ω - -c = -(X n ω - c) := by ring
  rw [heq, abs_neg]

theorem sub (hX : ConvergesInProbability μ X c) (hY : ConvergesInProbability μ Y d) :
    ConvergesInProbability μ (fun n ω => X n ω - Y n ω) (c - d) := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

theorem of_sub (hY : ConvergesInProbability μ Y c)
    (hXY : ConvergesInProbability μ (fun n ω => X n ω - Y n ω) 0) :
    ConvergesInProbability μ X c := by
  simpa only [sub_add_cancel, zero_add] using hXY.add hY

/-- Remove an initial block whose deterministic bound can be made
arbitrarily small, after sufficiently many rows. This is the double-limit
argument used three times in Proposition 3.2. -/
theorem of_arbitrarily_close
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ Y : ∀ n, Ω n → ℝ,
      ConvergesInProbability μ Y 0 ∧
        ∀ᶠ n in atTop, ∀ ω, |X n ω - Y n ω| ≤ ε) :
    ConvergesInProbability μ X 0 := by
  intro ε hε
  obtain ⟨Y, hY, hclose⟩ := happrox (ε / 2) (half_pos hε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hY (ε / 2) (half_pos hε)) (Eventually.of_forall fun _ => measureReal_nonneg)
  filter_upwards [hclose] with n hn
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  have hb := abs_sub_le (X n ω) (Y n ω) 0
  have hc := hn ω
  change ε < |X n ω - 0| at hω
  change ε / 2 < |Y n ω - 0|
  linarith

end Luce.ConvergesInProbability
