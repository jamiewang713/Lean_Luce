import Luce.Section3Interior
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform concentration of monotone races

The finite-grid part of the race law in Section 3, including construction of
the grid from continuity of the limiting function.  Uniform error events use
outer probability, so no measurability of an uncountable supremum is needed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- A continuous function on a compact time interval admits a finite grid
whose bracketing values have arbitrarily small oscillation. -/
theorem exists_finite_oscillation_grid {f : ℝ → ℝ} {T δ : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hδ : 0 < δ) :
    ∃ grid : Finset ℝ, (∀ t ∈ grid, t ∈ Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, ∃ a ∈ grid, ∃ b ∈ grid,
        a ≤ t ∧ t ≤ b ∧ |f t - f a| ≤ δ ∧ |f b - f t| ≤ δ := by
  classical
  obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) δ hδ
  obtain ⟨centers, hcenters, hfinite, hcover⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).finite_cover_balls
      (show 0 < r / 3 by linarith)
  let lo : ℝ → ℝ := fun c => max 0 (c - r / 3)
  let hi : ℝ → ℝ := fun c => min T (c + r / 3)
  let grid := hfinite.toFinset.image lo ∪ hfinite.toFinset.image hi
  have hlo : ∀ c ∈ centers, lo c ∈ Icc 0 T := by
    intro c hc
    have hc' := hcenters hc
    exact ⟨le_max_left _ _, max_le (hc'.1.trans hc'.2) (by linarith [hc'.2])⟩
  have hhi : ∀ c ∈ centers, hi c ∈ Icc 0 T := by
    intro c hc
    have hc' := hcenters hc
    exact ⟨le_min (hc'.1.trans hc'.2) (by linarith [hc'.1]), min_le_left _ _⟩
  refine ⟨grid, ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
      exact hlo c (hfinite.mem_toFinset.mp hc)
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
      exact hhi c (hfinite.mem_toFinset.mp hc)
  · intro t ht
    obtain ⟨c, hc, htc⟩ := Set.mem_iUnion₂.mp (hcover ht)
    have hdist : |t - c| < r / 3 := by simpa [Metric.mem_ball, Real.dist_eq] using htc
    have hlow : c - r / 3 < t := by have := (abs_lt.mp hdist).1; linarith
    have hupp : t < c + r / 3 := by have := (abs_lt.mp hdist).2; linarith
    have hat : lo c ≤ t := max_le ht.1 hlow.le
    have htb : t ≤ hi c := le_min ht.2 hupp.le
    have hta : dist t (lo c) < r := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hat)]
      have h := le_max_right 0 (c - r / 3)
      dsimp [lo]
      linarith
    have hbt : dist (hi c) t < r := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htb)]
      have h := min_le_right T (c + r / 3)
      dsimp [hi]
      linarith
    refine ⟨lo c, Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨c, hfinite.mem_toFinset.mpr hc, rfl⟩), hi c,
      Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨c, hfinite.mem_toFinset.mpr hc, rfl⟩), hat, htb, ?_, ?_⟩
    · simpa [Real.dist_eq] using (hmod t ht (lo c) (hlo c hc) hta).le
    · simpa [Real.dist_eq] using (hmod (hi c) (hhi c hc) t ht hbt).le

section Probability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}

/-- Pointwise convergence in probability of monotone sample paths to a
continuous limit is uniform on compact time intervals. -/
theorem monotone_uniform_convergence_in_probability
    {X : ∀ n, Ω n → ℝ → ℝ} {f : ℝ → ℝ} {T : ℝ}
    (hmono : ∀ n ω, Monotone (X n ω)) (hf : ContinuousOn f (Icc 0 T))
    (hpoint : ∀ t ∈ Icc 0 T, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |X n ω t - f t|}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => μ n {ω | ∃ t ∈ Icc 0 T, ε ≤ |X n ω t - f t|}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨grid, hgrid, hcover⟩ := exists_finite_oscillation_grid hf
    (show 0 < ε / 3 by linarith)
  have hbound : ∀ n, μ n {ω | ∃ t ∈ Icc 0 T, ε ≤ |X n ω t - f t|} ≤
      ∑ t ∈ grid, μ n {ω | ε / 3 ≤ |X n ω t - f t|} := by
    intro n
    calc
      μ n {ω | ∃ t ∈ Icc 0 T, ε ≤ |X n ω t - f t|}
        ≤ μ n (⋃ t ∈ grid, {ω | ε / 3 ≤ |X n ω t - f t|}) := by
          apply measure_mono
          intro ω hω
          by_contra hbad
          have hgood : ∀ t ∈ grid, |X n ω t - f t| ≤ ε / 3 := by
            intro t ht
            have : ¬ ε / 3 ≤ |X n ω t - f t| := by
              intro h
              exact hbad (Set.mem_iUnion₂.mpr ⟨t, ht, h⟩)
            exact (lt_of_not_ge this).le
          obtain ⟨t, ht, herr⟩ := hω
          have h := monotone_grid_error (hmono n ω) grid (Icc 0 T) hgood hcover t ht
          linarith
      _ ≤ ∑ t ∈ grid, μ n {ω | ε / 3 ≤ |X n ω t - f t|} := measure_biUnion_finset_le _ _
  have hsum := tendsto_finsetSum grid (fun t ht => hpoint t (hgrid t ht)
    (ε / 3) (by linarith))
  simp only [Finset.sum_const_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) hbound

/-- The remaining-rate version of the uniform race theorem. -/
theorem antitone_uniform_convergence_in_probability
    {X : ∀ n, Ω n → ℝ → ℝ} {f : ℝ → ℝ} {T : ℝ}
    (hmono : ∀ n ω, Antitone (X n ω)) (hf : ContinuousOn f (Icc 0 T))
    (hpoint : ∀ t ∈ Icc 0 T, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |X n ω t - f t|}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => μ n {ω | ∃ t ∈ Icc 0 T, ε ≤ |X n ω t - f t|}) atTop (𝓝 0) := by
  have h := monotone_uniform_convergence_in_probability
    (X := fun n ω t => -X n ω t) (f := fun t => -f t)
    (fun n ω _ _ hab => neg_le_neg (hmono n ω hab)) hf.neg
    (by simpa only [neg_sub_neg, abs_sub_comm] using hpoint)
  simpa only [neg_sub_neg, abs_sub_comm] using h

/-- Vanishing variance and convergent expectations imply convergence in
probability to a deterministic value, by Chebyshev's inequality. -/
theorem concentration_of_variance_tendsto_zero [∀ n, IsFiniteMeasure (μ n)]
    {X : ∀ n, Ω n → ℝ} {c : ℝ} (hX : ∀ n, MemLp (X n) 2 (μ n))
    (hvar : Tendsto (fun n => variance (X n) (μ n)) atTop (𝓝 0))
    (hmean : Tendsto (fun n => ∫ ω, X n ω ∂μ n) atTop (𝓝 c)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {ω | ε ≤ |X n ω - c|}) atTop (𝓝 0) := by
  intro ε hε
  have hmean' : ∀ᶠ n in atTop, |(∫ ω, X n ω ∂μ n) - c| < ε / 2 := by
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.mp hmean) (ε / 2) (by linarith)
  have hbound : ∀ᶠ n in atTop, μ n {ω | ε ≤ |X n ω - c|} ≤
      ENNReal.ofReal (variance (X n) (μ n) / (ε / 2)^2) := by
    filter_upwards [hmean'] with n hn
    refine (measure_mono ?_).trans (meas_ge_le_variance_div_sq (hX n) (by linarith : 0 < ε / 2))
    intro ω hω
    have h := abs_sub_le (X n ω) (∫ ω, X n ω ∂μ n) c
    dsimp at hω ⊢
    linarith
  have hlim : Tendsto (fun n => ENNReal.ofReal (variance (X n) (μ n) / (ε / 2)^2))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (hvar.div_const ((ε / 2)^2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) hbound

end Probability
end Luce
