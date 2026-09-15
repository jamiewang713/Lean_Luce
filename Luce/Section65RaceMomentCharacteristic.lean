import Luce.Section65GaussianVector
import Luce.Section65MomentCharacteristic
import Luce.Section5BulkPointProbability
import Luce.Section5FiniteStatistic

noncomputable section
open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology BigOperators ENNReal
namespace Luce.Section6

theorem memLp_race_permutation_statistic65 {n : ℕ} (w : Weights n)
    (F : Equiv.Perm (Fin n) → ℝ) (p : ℝ≥0∞) :
    MemLp (fun z => F (raceRankPermutation z)) p (exponentialRace w) := by
  classical
  apply MemLp.of_bound (measurable_race_permutation_statistic F).aestronglyMeasurable
    (∑ R : Equiv.Perm (Fin n), ‖F R‖)
  filter_upwards [] with z
  exact Finset.single_le_sum (fun R _ => norm_nonneg (F R)) (Finset.mem_univ (raceRankPermutation z))

theorem race_linear_moment_tendsto65 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : WeightArray) (X : ∀ n, Equiv.Perm (Fin n) → ι → ℝ)
    (h : ∀ r : ι → ℕ, Tendsto (fun n => ∫ clocks, ∏ i, X n (raceRankPermutation clocks) i^(r i)
      ∂exponentialRace (w n)) atTop (𝓝 (∏ i, gaussianMoment65 1 (r i))))
    (t : ι → ℝ) (k : ℕ) :
    Tendsto (fun n => ∫ clocks, linearCombination65 t (X n (raceRankPermutation clocks))^k
      ∂exponentialRace (w n)) atTop
      (𝓝 (∫ z, linearCombination65 t z^k ∂standardNormalVector ι)) := by
  have he (n : ℕ) : (∫ clocks, linearCombination65 t (X n (raceRankPermutation clocks))^k
      ∂exponentialRace (w n)) = ∑ v : Fin k → ι, (∏ j : Fin k, t (v j))*
        ∫ clocks, ∏ i, X n (raceRankPermutation clocks) i^(multiplicity65 v i)
          ∂exponentialRace (w n) := by
    simp_rw [linearCombination65_power]
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro v hv
      exact integrable_race_permutation_statistic (w n) (fun R =>
        (∏ j : Fin k, t (v j))*∏ i, X n R i^(multiplicity65 v i))
  simp_rw [he, standardNormalVector_linear_moment65]
  apply tendsto_finsetSum
  intro v hv
  exact (h (multiplicity65 v)).const_mul _

theorem race_moments_characteristic65 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : WeightArray) (X : ∀ n, Equiv.Perm (Fin n) → ι → ℝ)
    (h : ∀ r : ι → ℕ, Tendsto (fun n => ∫ clocks, ∏ i, X n (raceRankPermutation clocks) i^(r i)
      ∂exponentialRace (w n)) atTop (𝓝 (∏ i, gaussianMoment65 1 (r i))))
    (t : ι → ℝ) :
    Tendsto (fun n => ∫ clocks, Complex.exp ((linearCombination65 t
      (X n (raceRankPermutation clocks)) : ℂ)*I) ∂exponentialRace (w n)) atTop
      (𝓝 (∫ z, Complex.exp ((linearCombination65 t z : ℂ)*I) ∂standardNormalVector ι)) := by
  let Y (n : ℕ) (clocks : Fin n → ℝ) := linearCombination65 t (X n (raceRankPermutation clocks))
  have hm (n : ℕ) : Measurable (Y n) :=
    measurable_race_permutation_statistic (fun R => linearCombination65 t (X n R))
  have ht : Measurable (linearCombination65 t) := by unfold linearCombination65; fun_prop
  let μ (n : ℕ) := (exponentialRace (w n)).map (Y n)
  let ν := (standardNormalVector ι).map (linearCombination65 t)
  letI (n : ℕ) : IsProbabilityMeasure (μ n) := Measure.isProbabilityMeasure_map (hm n).aemeasurable
  letI : IsProbabilityMeasure (standardNormalVector ι) := by unfold standardNormalVector; infer_instance
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map ht.aemeasurable
  have hμ (n k : ℕ) : MemLp id k (μ n) := by
    rw [memLp_map_measure_iff (by fun_prop) (hm n).aemeasurable]
    exact memLp_race_permutation_statistic65 (w n) (fun R => linearCombination65 t (X n R)) k
  have hν (k : ℕ) : MemLp id k ν := by
    rw [memLp_map_measure_iff (by fun_prop) ht.aemeasurable]
    exact standardNormalVector_linear_memLp65 t k
  have he : Integrable (fun x : ℝ => Real.exp (2*|x|)) ν := by
    rw [integrable_map_measure (by fun_prop) ht.aemeasurable]
    exact standardNormalVector_linear_expabs65 t
  have hh : ∀ k : ℕ, Tendsto (fun n => ∫ x, x^k ∂μ n) atTop (𝓝 (∫ x, x^k ∂ν)) := by
    intro k
    have heμ (n : ℕ) : (∫ x, x^k ∂μ n) = ∫ clocks, (Y n clocks)^k ∂exponentialRace (w n) := by
      exact integral_map (hm n).aemeasurable (by fun_prop)
    have heν : (∫ x, x^k ∂ν) = ∫ z, linearCombination65 t z^k ∂standardNormalVector ι := by
      exact integral_map ht.aemeasurable (by fun_prop)
    simp only [heμ,heν]
    exact race_linear_moment_tendsto65 w X h t k
  have hlim := charFun_one_tendsto_of_moments μ ν hμ hν he hh
  have heμ (n : ℕ) : charFun (μ n) 1 =
      ∫ clocks, Complex.exp ((Y n clocks : ℂ)*I) ∂exponentialRace (w n) := by
    rw [charFun_apply_real]
    simp only [Complex.ofReal_one,one_mul]
    exact integral_map (hm n).aemeasurable (by fun_prop)
  have heν : charFun ν 1 =
      ∫ z, Complex.exp ((linearCombination65 t z : ℂ)*I) ∂standardNormalVector ι := by
    rw [charFun_apply_real]
    simp only [Complex.ofReal_one,one_mul]
    exact integral_map ht.aemeasurable (by fun_prop)
  simpa only [heμ,heν,Y] using hlim

end Luce.Section6
