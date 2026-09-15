import Luce.Section65RaceMomentCharacteristic

noncomputable section
open MeasureTheory ProbabilityTheory Filter Complex WithLp
open scoped Topology BigOperators BoundedContinuousFunction
namespace Luce.Section6

/-- Finite-dimensional Gaussian convergence from characteristic functions,
for statistics of the actual finite exponential races. -/
theorem race_characteristic_clt65 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : WeightArray) (X : ∀ n, Equiv.Perm (Fin n) → ι → ℝ)
    (h : ∀ t : ι → ℝ, Tendsto (fun n => ∫ clocks, Complex.exp ((linearCombination65 t
      (X n (raceRankPermutation clocks)) : ℂ)*I) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ z, Complex.exp ((linearCombination65 t z : ℂ)*I) ∂standardNormalVector ι)))
    (F : (ι → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ clocks, F (X n (raceRankPermutation clocks)) ∂exponentialRace (w n))
      atTop (𝓝 (∫ z, F z ∂standardNormalVector ι)) := by
  let E := EuclideanSpace ℝ ι
  let Y (n : ℕ) (clocks : Fin n → ℝ) : E := toLp 2 (X n (raceRankPermutation clocks))
  have hm (n : ℕ) : Measurable (Y n) :=
    measurable_race_permutation_statistic (fun R => toLp 2 (X n R))
  have ht : Measurable (toLp 2 : (ι → ℝ) → E) := (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable
  let μ (n : ℕ) : ProbabilityMeasure E :=
    ⟨(exponentialRace (w n)).map (Y n), Measure.isProbabilityMeasure_map (hm n).aemeasurable⟩
  letI : IsProbabilityMeasure (standardNormalVector ι) := by unfold standardNormalVector; infer_instance
  let ν : ProbabilityMeasure E :=
    ⟨(standardNormalVector ι).map (toLp 2), Measure.isProbabilityMeasure_map ht.aemeasurable⟩
  have hc (t : E) : Tendsto (fun n => charFun (μ n) t) atTop (𝓝 (charFun ν t)) := by
    have hh := h (fun i => t i)
    have he (z : ι → ℝ) : inner ℝ (toLp 2 z : E) t = linearCombination65 (fun i => t i) z := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, linearCombination65]
    have heμ (n : ℕ) : charFun (μ n) t = ∫ clocks,
        Complex.exp ((linearCombination65 (fun i => t i) (X n (raceRankPermutation clocks)) : ℂ)*I)
          ∂exponentialRace (w n) := by
      change (∫ x : E, Complex.exp ((inner ℝ x t : ℂ)*I)
        ∂(exponentialRace (w n)).map (Y n)) = _
      rw [integral_map (hm n).aemeasurable
        (f := fun x : E => Complex.exp ((inner ℝ x t : ℂ)*I)) (by fun_prop)]
      simp only [Y,he]
    have heν : charFun ν t = ∫ z,
        Complex.exp ((linearCombination65 (fun i => t i) z : ℂ)*I) ∂standardNormalVector ι := by
      change (∫ x : E, Complex.exp ((inner ℝ x t : ℂ)*I)
        ∂(standardNormalVector ι).map (toLp 2)) = _
      rw [integral_map ht.aemeasurable
        (f := fun x : E => Complex.exp ((inner ℝ x t : ℂ)*I)) (by fun_prop)]
      simp only [he]
    simpa only [heμ,heν] using hh
  have hweak : Tendsto μ atTop (𝓝 ν) := ProbabilityMeasure.tendsto_of_tendsto_charFun hc
  let G : E →ᵇ ℝ := F.compContinuous ⟨ofLp, by fun_prop⟩
  have hh := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) G
  have heμ (n : ℕ) : (∫ x, G x ∂(μ n : Measure E)) =
      ∫ clocks, F (X n (raceRankPermutation clocks)) ∂exponentialRace (w n) := by
    exact integral_map (hm n).aemeasurable G.continuous.measurable.aestronglyMeasurable
  have heν : (∫ x, G x ∂(ν : Measure E)) = ∫ z, F z ∂standardNormalVector ι := by
    exact integral_map ht.aemeasurable G.continuous.measurable.aestronglyMeasurable
  simpa only [heμ,heν] using hh

/-- Finite-dimensional Gaussian convergence from mixed moments, for
statistics of the actual finite exponential races. -/
theorem race_moments_clt65 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : WeightArray) (X : ∀ n, Equiv.Perm (Fin n) → ι → ℝ)
    (h : ∀ r : ι → ℕ, Tendsto (fun n => ∫ clocks, ∏ i, X n (raceRankPermutation clocks) i^(r i)
      ∂exponentialRace (w n)) atTop (𝓝 (∏ i, gaussianMoment65 1 (r i))))
    (F : (ι → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ clocks, F (X n (raceRankPermutation clocks)) ∂exponentialRace (w n))
      atTop (𝓝 (∫ z, F z ∂standardNormalVector ι)) :=
  race_characteristic_clt65 w X (race_moments_characteristic65 w X h) F

end Luce.Section6
