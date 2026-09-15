import Luce.CompactLaplaceApproximation
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # From compact approximation to convergence of laws

These analytic helpers use measurable real tests on arbitrary measurable
spaces. They do not identify the measurable space with the weak Borel space.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction Polynomial

namespace Luce

lemma integral_sub_abs_le_uniform
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {f g : S → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) {ε : ℝ}
    (hε : ∀ s, |f s - g s| ≤ ε) :
    |(∫ s, f s ∂μ) - ∫ s, g s ∂μ| ≤ ε := by
  rw [← integral_sub hf hg, ← Real.norm_eq_abs]
  simpa using norm_integral_le_of_norm_le_const
    (μ := μ) (f := fun s => f s - g s)
    (ae_of_all _ (fun s => (by simpa only [Real.norm_eq_abs] using hε s)))

/-- Convergence of integrals is preserved under global uniform approximation
of a bounded measurable test, even when the source sigma algebra is unrelated
to a topology. -/
theorem tendsto_integral_of_uniform_approximation
    {S : Type*} [MeasurableSpace S] (μ : ℕ → Measure S) (ν : Measure S)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hbound : ∀ s, |f s| ≤ B)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : S → ℝ, Measurable g ∧
      (∀ s, |g s - f s| ≤ ε) ∧
      Tendsto (fun n => ∫ s, g s ∂μ n) atTop (𝓝 (∫ s, g s ∂ν))) :
    Tendsto (fun n => ∫ s, f s ∂μ n) atTop (𝓝 (∫ s, f s ∂ν)) := by
  have hfint (ρ : Measure S) [IsProbabilityMeasure ρ] : Integrable f ρ :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ (fun s => by
      simpa only [Real.norm_eq_abs] using hbound s))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g, hg, hgf, hconv⟩ := happrox (ε / 3) (by positivity)
  have hgint (ρ : Measure S) [IsProbabilityMeasure ρ] : Integrable g ρ := by
    refine Integrable.of_bound hg.aestronglyMeasurable (B + ε / 3) (ae_of_all _ ?_)
    intro s
    rw [Real.norm_eq_abs]
    have h := abs_add_le (g s - f s) (f s)
    simp only [sub_add_cancel] at h
    linarith [hgf s, hbound s]
  have hev := (Metric.tendsto_nhds.mp hconv) (ε / 3) (by positivity)
  filter_upwards [hev] with n hn
  rw [Real.dist_eq] at hn ⊢
  have hleft := integral_sub_abs_le_uniform (μ n) (hgint (μ n)) (hfint (μ n)) hgf
  have hright := integral_sub_abs_le_uniform ν (hgint ν) (hfint ν) hgf
  calc
    |(∫ s, f s ∂μ n) - ∫ s, f s ∂ν| ≤
        |(∫ s, g s ∂μ n) - ∫ s, f s ∂μ n| +
        |(∫ s, g s ∂μ n) - ∫ s, g s ∂ν| +
        |(∫ s, g s ∂ν) - ∫ s, f s ∂ν| := by
      calc
        _ = |((∫ s, f s ∂μ n) - ∫ s, g s ∂μ n) +
          ((∫ s, g s ∂μ n) - ∫ s, g s ∂ν) +
          ((∫ s, g s ∂ν) - ∫ s, f s ∂ν)| := by congr 1; ring
        _ ≤ _ := by
          have h1 := abs_add_le ((∫ s, f s ∂μ n) - ∫ s, g s ∂μ n)
            ((∫ s, g s ∂μ n) - ∫ s, g s ∂ν)
          have h2 := abs_add_le (((∫ s, f s ∂μ n) - ∫ s, g s ∂μ n) +
            ((∫ s, g s ∂μ n) - ∫ s, g s ∂ν))
            ((∫ s, g s ∂ν) - ∫ s, f s ∂ν)
          rw [abs_sub_comm (∫ s, f s ∂μ n) (∫ s, g s ∂μ n)] at h1
          linarith
    _ < ε := by linarith

/-- Scalar continuous transformations of one bounded algebra element can be
approximated globally by elements of the same algebra. -/
theorem exists_algebra_uniform_approximation_comp
    {S M : Type*} [TopologicalSpace M]
    (J : S → M) (A : Subalgebra ℝ C(M, ℝ))
    (a : C(M, ℝ)) (ha : a ∈ A) {B : ℝ} (hbound : ∀ s, |a (J s)| ≤ B)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) {ε : ℝ} (hε : 0 < ε) :
    ∃ b ∈ A, ∀ s, |b (J s) - ψ (a (J s))| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    (-B) B ψ hψ.continuousOn ε hε
  let b : A := Polynomial.aeval (⟨a, ha⟩ : A) p
  refine ⟨b, b.property, fun s => ?_⟩
  have hs := hp (a (J s)) (abs_le.mp (hbound s))
  change |((Polynomial.aeval (⟨a, ha⟩ : A) p : A) : C(M, ℝ)) (J s) - ψ (a (J s))| < ε
  rw [Polynomial.aeval_subalgebra_coe, Polynomial.aeval_continuousMap_apply]
  exact hs

/-- A continuous scalar transformation of a bounded algebra test inherits
convergence of expectations from the algebra. -/
theorem tendsto_integral_continuous_comp_of_subalgebra
    {S M : Type*} [MeasurableSpace S] [TopologicalSpace M]
    (μ : ℕ → Measure S) (ν : Measure S)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (J : S → M) (A : Subalgebra ℝ C(M, ℝ))
    (hAmeas : ∀ a ∈ A, Measurable (fun s => a (J s)))
    (hAconv : ∀ a ∈ A,
      Tendsto (fun n => ∫ s, a (J s) ∂μ n) atTop (𝓝 (∫ s, a (J s) ∂ν)))
    (a : C(M, ℝ)) (ha : a ∈ A) {B : ℝ} (hbound : ∀ s, |a (J s)| ≤ B)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hψbound : ∀ s, |ψ (a (J s))| ≤ C) :
    Tendsto (fun n => ∫ s, ψ (a (J s)) ∂μ n)
      atTop (𝓝 (∫ s, ψ (a (J s)) ∂ν)) := by
  refine tendsto_integral_of_uniform_approximation μ ν
    (hψ.measurable.comp (hAmeas a ha)) hψbound ?_
  intro ε hε
  obtain ⟨b, hb, hbapprox⟩ :=
    exists_algebra_uniform_approximation_comp J A a ha hbound ψ hψ hε
  exact ⟨fun s => b (J s), hAmeas b hb, fun s => (hbapprox s).le, hAconv b hb⟩

/-- Clipping a real number to a symmetric bounded interval. -/
def symmetricClip (B x : ℝ) : ℝ := max (-B) (min B x)

lemma continuous_symmetricClip (B : ℝ) : Continuous (symmetricClip B) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma abs_symmetricClip_le {B : ℝ} (hB : 0 ≤ B) (x : ℝ) :
    |symmetricClip B x| ≤ B := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma symmetricClip_eq_self {B x : ℝ} (hx : |x| ≤ B) : symmetricClip B x = x := by
  rcases abs_le.mp hx with ⟨hxlo, hxhi⟩
  simp only [symmetricClip, min_eq_right hxhi, max_eq_right hxlo]

lemma abs_symmetricClip_sub_le {B x y : ℝ} (hy : |y| ≤ B) :
    |symmetricClip B x - y| ≤ |x - y| := by
  calc
    _ = |symmetricClip B x - symmetricClip B y| := by rw [symmetricClip_eq_self hy]
    _ ≤ |min B x - min B y| := by
      simpa only [symmetricClip, sub_self, abs_zero,
        max_eq_right (abs_nonneg (min B x - min B y))] using
        abs_max_sub_max_le_max (-B) (min B x) (-B) (min B y)
    _ ≤ |x - y| := by
      simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (x - y))] using
        abs_min_sub_min_le_max B x B y

/-- A local uniform approximation controls expectations up to the mass
outside the approximation set. -/
lemma integral_sub_abs_le_on_set
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {f g : S → ℝ} (hf : Measurable f) (hg : Measurable g) {B ε : ℝ}
    (hfbound : ∀ s, |f s| ≤ B) (hgbound : ∀ s, |g s| ≤ B) (hε : 0 ≤ ε)
    {K : Set S} (hK : MeasurableSet K) (happrox : ∀ s ∈ K, |f s - g s| ≤ ε) :
    |(∫ s, f s ∂μ) - ∫ s, g s ∂μ| ≤ ε + 2 * B * μ.real Kᶜ := by
  have hfint : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ (fun s => by simpa only [Real.norm_eq_abs] using hfbound s))
  have hgint : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable B
    (ae_of_all _ (fun s => by simpa only [Real.norm_eq_abs] using hgbound s))
  have hint : Integrable (fun s => |f s - g s|) μ := (hfint.sub hgint).norm
  have henv : Integrable (fun s => ε + Kᶜ.indicator (fun _ => 2 * B) s) μ :=
    (integrable_const ε).add ((integrable_const (2 * B)).indicator hK.compl)
  calc
    _ = |∫ s, f s - g s ∂μ| := by rw [integral_sub hfint hgint]
    _ ≤ ∫ s, |f s - g s| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun s => f s - g s)
    _ ≤ ∫ s, ε + Kᶜ.indicator (fun _ => 2 * B) s ∂μ := by
      apply integral_mono_ae hint henv
      apply ae_of_all
      intro s
      change |f s - g s| ≤ ε + Kᶜ.indicator (fun _ => 2 * B) s
      by_cases hs : s ∈ K
      · rw [Set.indicator_of_notMem (show s ∉ Kᶜ by simpa using hs), add_zero]
        exact happrox s hs
      · rw [Set.indicator_of_mem (show s ∈ Kᶜ from hs)]
        have h := abs_sub (f s) (g s)
        linarith [hfbound s, hgbound s]
    _ = _ := by
      rw [integral_add (integrable_const ε) ((integrable_const (2 * B)).indicator hK.compl),
        integral_indicator hK.compl]
      simp [measureReal_def, mul_comm]

/-- Convergence on a bounded measurable moment algebra, together with
tightness on compact sets, implies convergence for every bounded continuous
state test. The sigma algebra need not contain every topologically open set.
-/
theorem tendsto_integral_boundedContinuousFunction_of_tight_algebra
    {S M : Type*} [TopologicalSpace S] [MeasurableSpace S] [TopologicalSpace M]
    (μ : ℕ → Measure S) (ν : Measure S)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (J : S → M) (hJ : IsInducing J)
    (A : Subalgebra ℝ C(M, ℝ)) (hA : A.SeparatesPoints)
    (hAmeas : ∀ a ∈ A, Measurable (fun s => a (J s)))
    (hAbound : ∀ a ∈ A, ∃ B : ℝ, ∀ s, |a (J s)| ≤ B)
    (hAconv : ∀ a ∈ A,
      Tendsto (fun n => ∫ s, a (J s) ∂μ n) atTop (𝓝 (∫ s, a (J s) ∂ν)))
    (K : ℕ → Set S) (hKcompact : ∀ N, IsCompact (K N))
    (hKmeas : ∀ N, MeasurableSet (K N))
    (hcover : ∀ s, ∀ᶠ N in atTop, s ∈ K N)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ N,
      ν.real (K N)ᶜ ≤ ε ∧ ∀ᶠ n in atTop, (μ n).real (K N)ᶜ ≤ ε)
    (F : S →ᵇ ℝ) :
    Tendsto (fun n => ∫ s, F s ∂μ n) atTop (𝓝 (∫ s, F s ∂ν)) := by
  have hFmeas : Measurable F :=
    measurable_boundedContinuousFunction_of_compact_exhaustion
      J hJ A hA hAmeas K hKcompact hcover F
  have hFbound (s : S) : |F s| ≤ ‖F‖ := by
    simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm s
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε / (16 * (‖F‖ + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδbound : 2 * ‖F‖ * δ ≤ ε / 8 := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 16 * (‖F‖ + 1))).mpr
    nlinarith [norm_nonneg F]
  obtain ⟨N, hνtail, hμtail⟩ := htight δ hδ
  obtain ⟨a, ha, haapprox⟩ :=
    exists_algebra_approximation_on_compact_of_isInducing
      J hJ A hA F (hKcompact N) (show 0 < ε / 8 by positivity)
  obtain ⟨B, hbound⟩ := hAbound a ha
  let g : S → ℝ := fun s => symmetricClip ‖F‖ (a (J s))
  have hgmeas : Measurable g :=
    (continuous_symmetricClip ‖F‖).measurable.comp (hAmeas a ha)
  have hgbound (s : S) : |g s| ≤ ‖F‖ := abs_symmetricClip_le (norm_nonneg F) _
  have hgapprox (s : S) (hs : s ∈ K N) : |g s - F s| ≤ ε / 8 := by
    exact (abs_symmetricClip_sub_le (hFbound s)).trans
      (by simpa only [Real.norm_eq_abs] using (haapprox s hs).le)
  have hgconv : Tendsto (fun n => ∫ s, g s ∂μ n) atTop (𝓝 (∫ s, g s ∂ν)) :=
    tendsto_integral_continuous_comp_of_subalgebra μ ν J A hAmeas hAconv
      a ha hbound (symmetricClip ‖F‖) (continuous_symmetricClip ‖F‖) hgbound
  have hev := (Metric.tendsto_nhds.mp hgconv) (ε / 4) (by positivity)
  have hνerr := integral_sub_abs_le_on_set ν hgmeas hFmeas hgbound hFbound
    (show 0 ≤ ε / 8 by positivity) (hKmeas N) hgapprox
  have hνsmall : |(∫ s, g s ∂ν) - ∫ s, F s ∂ν| ≤ ε / 4 := by
    have h := mul_le_mul_of_nonneg_left hνtail (show 0 ≤ 2 * ‖F‖ by positivity)
    linarith
  filter_upwards [hev, hμtail] with n hn hntail
  rw [Real.dist_eq] at hn ⊢
  have hμerr := integral_sub_abs_le_on_set (μ n) hgmeas hFmeas hgbound hFbound
    (show 0 ≤ ε / 8 by positivity) (hKmeas N) hgapprox
  have hμsmall : |(∫ s, g s ∂μ n) - ∫ s, F s ∂μ n| ≤ ε / 4 := by
    have h := mul_le_mul_of_nonneg_left hntail (show 0 ≤ 2 * ‖F‖ by positivity)
    linarith
  have htriangle₁ := abs_sub_le (∫ s, F s ∂μ n) (∫ s, g s ∂μ n) (∫ s, F s ∂ν)
  have htriangle₂ := abs_sub_le (∫ s, g s ∂μ n) (∫ s, g s ∂ν) (∫ s, F s ∂ν)
  rw [abs_sub_comm (∫ s, F s ∂μ n) (∫ s, g s ∂μ n)] at htriangle₁
  linarith

end Luce
