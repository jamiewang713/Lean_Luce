import Luce.Section65RaceMomentCLT
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
open MeasureTheory Filter Complex
open scoped Topology BigOperators
namespace Luce.Section6

theorem imaginary_exp_lipschitz65 (x y : ℝ) :
    ‖Complex.exp ((x : ℂ)*I)-Complex.exp ((y : ℂ)*I)‖ ≤ |x-y| := by
  have he : Complex.exp ((x : ℂ)*I)-Complex.exp ((y : ℂ)*I) =
      Complex.exp ((y : ℂ)*I)*(Complex.exp (((x-y : ℝ) : ℂ)*I)-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he,norm_mul]
  have hy : ‖Complex.exp ((y : ℂ)*I)‖ = 1 := by simp [Complex.norm_exp,Complex.mul_re]
  rw [hy,one_mul]
  simpa [mul_comm,Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y))

theorem imaginary_exp_integrable65 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) (hX : Measurable X) :
    Integrable (fun ω => Complex.exp ((X ω : ℂ)*I)) P := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [] with ω
  simp [Complex.norm_exp,Complex.mul_re]

theorem characteristic_integral_l1_bound65 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hi : Integrable (fun ω => |X ω-Y ω|) P) :
    ‖(∫ ω, Complex.exp ((X ω : ℂ)*I) ∂P)-(∫ ω, Complex.exp ((Y ω : ℂ)*I) ∂P)‖ ≤
      ∫ ω, |X ω-Y ω| ∂P := by
  rw [← integral_sub (imaginary_exp_integrable65 P X hX) (imaginary_exp_integrable65 P Y hY)]
  exact norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall (fun ω => imaginary_exp_lipschitz65 _ _))

theorem race_characteristic_perturbation65 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : WeightArray) (X Y : ∀ n, Equiv.Perm (Fin n) → ι → ℝ)
    (hXY : ∀ i : ι, Tendsto (fun n => ∫ clocks,
      |X n (raceRankPermutation clocks) i-Y n (raceRankPermutation clocks) i| ∂exponentialRace (w n))
        atTop (𝓝 0))
    (t : ι → ℝ) :
    Tendsto (fun n => (∫ clocks, Complex.exp ((linearCombination65 t
      (X n (raceRankPermutation clocks)) : ℂ)*I) ∂exponentialRace (w n)) -
      (∫ clocks, Complex.exp ((linearCombination65 t
      (Y n (raceRankPermutation clocks)) : ℂ)*I) ∂exponentialRace (w n))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => ∑ i : ι, |t i| * ∫ clocks,
      |X n (raceRankPermutation clocks) i-Y n (raceRankPermutation clocks) i| ∂exponentialRace (w n))
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => (hXY i).const_mul |t i|)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ hlim
  intro n
  apply (characteristic_integral_l1_bound65 (exponentialRace (w n))
    (fun clocks => linearCombination65 t (X n (raceRankPermutation clocks)))
    (fun clocks => linearCombination65 t (Y n (raceRankPermutation clocks)))
    (measurable_race_permutation_statistic (fun R => linearCombination65 t (X n R)))
    (measurable_race_permutation_statistic (fun R => linearCombination65 t (Y n R)))
    (integrable_race_permutation_statistic (w n) (fun R =>
      |linearCombination65 t (X n R)-linearCombination65 t (Y n R)|))).trans
  have he : (∫ clocks, ∑ i : ι, |t i| *
      |X n (raceRankPermutation clocks) i-Y n (raceRankPermutation clocks) i| ∂exponentialRace (w n)) =
      ∑ i : ι, |t i| * ∫ clocks,
        |X n (raceRankPermutation clocks) i-Y n (raceRankPermutation clocks) i| ∂exponentialRace (w n) := by
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro i hi
      exact integrable_race_permutation_statistic (w n) (fun R => |t i| * |X n R i-Y n R i|)
  rw [← he]
  apply integral_mono
    (integrable_race_permutation_statistic (w n) (fun R => |linearCombination65 t (X n R)-linearCombination65 t (Y n R)|))
    (integrable_race_permutation_statistic (w n) (fun R => ∑ i, |t i| * |X n R i-Y n R i|))
  intro clocks
  simp only [linearCombination65,← Finset.sum_sub_distrib,← mul_sub,← abs_mul]
  exact Finset.abs_sum_le_sum_abs _ _

end Luce.Section6
