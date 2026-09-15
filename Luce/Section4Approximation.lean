import Luce.Section4Count

/-! # Removing the terminal cutoff

Source: `fixed_points.tex:953–956`. The full and interior random measures
are exactly equal whenever the terminal count is zero. A scalar
converging-together argument turns this equality into convergence of tests.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

namespace Luce

/-- Scalar converging-together lemma, with every real-limsup boundedness
condition stated. In the application p is an actual probability. -/
theorem tendsto_of_terminal_approximation
    (u : ℕ → ℝ) (v : ℝ → ℕ → ℝ) (a : ℝ → ℝ) (p : ℝ → ℕ → ℝ) (L : ℝ)
    (hp : ∀ α, IsBoundedUnder (· ≤ ·) atTop (p α))
    (htail : Tendsto (fun α => limsup (p α) atTop) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (ha : Tendsto a (𝓝[<] (1 : ℝ)) (𝓝 L))
    (hv : ∀ α, α < 1 → Tendsto (v α) atTop (𝓝 (a α)))
    (happrox : ∀ α, α < 1 → ∀ n, |u n - v α n| ≤ p α n) :
    Tendsto u atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have hpa := htail.eventually (Iio_mem_nhds hthird)
  have haa := (Metric.tendsto_nhds.mp ha) (ε / 3) hthird
  have hlt : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), α < 1 := self_mem_nhdsWithin
  obtain ⟨α, hα, hpa, haa⟩ := (hlt.and (hpa.and haa)).exists
  have hpn := eventually_lt_of_limsup_lt hpa (hp α)
  have hvn := (Metric.tendsto_nhds.mp (hv α hα)) (ε / 3) hthird
  filter_upwards [hpn, hvn] with n hn hvn
  rw [Real.dist_eq] at haa hvn ⊢
  have htri : |u n - L| ≤ |u n - v α n| + |v α n - a α| + |a α - L| := by
    have h1 := dist_triangle (u n) (v α n) L
    have h2 := dist_triangle (v α n) (a α) L
    simp only [Real.dist_eq] at h1 h2
    linarith
  linarith [happrox α hα n]

/-- An integrable test taking values in [0,1] changes in expectation by at
most the probability of the event on which it changes. -/
lemma abs_integral_sub_le_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F G : Ω → ℝ}
    (hF : Integrable F P) (hG : Integrable G P)
    (hFb : ∀ ω, F ω ∈ Icc (0 : ℝ) 1) (hGb : ∀ ω, G ω ∈ Icc (0 : ℝ) 1)
    {bad : Set Ω} (hbad : MeasurableSet bad)
    (heq : ∀ᵐ ω ∂P, ω ∉ bad → F ω = G ω) :
    |(∫ ω, F ω ∂P) - ∫ ω, G ω ∂P| ≤ P.real bad := by
  rw [← integral_sub hF hG, ← Real.norm_eq_abs]
  have hi : Integrable (bad.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const _).indicator hbad
  have h := norm_integral_le_of_norm_le hi (f := fun ω => F ω - G ω) ?_
  · simpa only [integral_indicator_const _ hbad, smul_eq_mul, mul_one] using h
  · filter_upwards [heq] with ω hω
    by_cases hb : ω ∈ bad
    · rw [indicator_of_mem hb, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [(hFb ω).1, (hFb ω).2, (hGb ω).1, (hGb ω).2]
    · rw [indicator_of_notMem hb, hω hb, sub_self, norm_zero]

/-- Every missing atom would be a terminal fixed point, so a zero terminal
count gives equality of the actual finite measures, not just their masses. -/
theorem fixedPoints_eq_interior_of_tail_zero {n : ℕ} (e : Fin n → ℝ)
    (hinj : Function.Injective e) (α : ℝ) (hz : tailFixedPointCount e α = 0) :
    fixedPoints (raceDraw e) = interiorFixedPoints α (raceDraw e) := by
  classical
  have hselected (k : Fin n) (hk : (raceDraw e).symm k = k) :
      ((k.val : ℝ) + 1) / n ≤ α := by
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt k.isLt
    apply le_of_not_gt
    intro htail
    have hmem : k ∈ Finset.univ.filter (fun j : Fin n =>
        α * (n : ℝ) < (j.val : ℝ) + 1 ∧ rankOf e j = j.val + 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (lt_div_iff₀ hn).mp htail,
        (raceDraw_fixed_iff_rankOf e hinj k).mp hk⟩
    have hempty := Finset.card_eq_zero.mp hz
    exact Finset.notMem_empty k (hempty ▸ hmem)
  unfold fixedPoints interiorFixedPoints
  congr 1
  funext k
  have hloc := (section3Location n k).property.2
  change ((k.val : ℝ) + 1) / n ≤ 1 at hloc
  by_cases hk : (raceDraw e).symm k = k
  · simp [hk, hloc, hselected k hk]
  · simp [hk]

lemma measurable_interiorFixedPoints_race {n : ℕ} (w : Weights n) (α : ℝ) :
    Measurable (fun e : Fin n → ℝ => interiorFixedPoints α (raceDraw e)) := by
  have heq : (raceInteriorBernoulli w α).pointMeasure (section3Location n) =
      (fun e => interiorFixedPoints α (raceDraw e)) :=
    funext (raceInteriorBernoulli_pointMeasure w α)
  rw [← heq]
  exact (raceInteriorBernoulli w α).measurable_pointMeasure (section3Location n)

/-- The Laplace-test cutoff error is bounded by the exact tail probability. -/
theorem section4_laplace_cutoff_error {n : ℕ} (w : Weights n) (α : ℝ)
    (g : Icc (0 : ℝ) 1 →ᵇ ℝ≥0) :
    |(∫ e, pointLaplace (fun x => (g x : ℝ)) (fixedPoints (raceDraw e)) ∂exponentialRace w) -
      ∫ e, pointLaplace (fun x => (g x : ℝ)) (interiorFixedPoints α (raceDraw e))
        ∂exponentialRace w| ≤
      (exponentialRace w).real {e | 0 < tailFixedPointCount e α} := by
  have hg := (NNReal.continuous_coe.comp g.continuous).measurable
  have hb := pointLaplace_mem_Icc (fun x => (g x : ℝ)) (fun x => (g x).coe_nonneg)
  have hi (a : ℝ) : Integrable (fun e => pointLaplace (fun x => (g x : ℝ))
      (interiorFixedPoints a (raceDraw e))) (exponentialRace w) := by
    apply Integrable.of_bound
      ((measurable_pointLaplace _ hg (fun x => (g x).coe_nonneg)).comp
        (measurable_interiorFixedPoints_race w a)).aestronglyMeasurable 1
    exact Eventually.of_forall fun e => by
      change ‖pointLaplace (fun x => (g x : ℝ)) (interiorFixedPoints a (raceDraw e))‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (hb _).1]
      exact (hb _).2
  apply abs_integral_sub_le_probability (exponentialRace w) (hi 1) (hi α)
    (fun _ => hb _) (fun _ => hb _)
    (measurableSet_lt measurable_const (measurable_tailFixedPointCount α))
  filter_upwards [exponentialRace_injective_ae w] with e he
  intro hbad
  have hz : tailFixedPointCount e α = 0 := Nat.eq_zero_of_not_pos hbad
  exact congrArg (pointLaplace (fun x => (g x : ℝ)))
    (fixedPoints_eq_interior_of_tail_zero e he α hz)

end Luce
