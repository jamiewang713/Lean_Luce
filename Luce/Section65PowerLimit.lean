import Luce.Section65PowerProjection
import Luce.Section65TotalCoreExpectation

noncomputable section
open MeasureTheory Filter Complex
open scoped Topology BigOperators BoundedContinuousFunction
namespace Luce.Section6

theorem power_race_clt65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (L : ℕ) (F : (Fin L → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ clocks,
      F (normalizedCycleVector (raceRankPermutation clocks) left right L) ∂exponentialRace (w n))
      atTop (𝓝 (∫ z, F z ∂standardNormalVector (Fin L))) := by
  classical
  let X (n : ℕ) (R : Equiv.Perm (Fin n)) := normalizedCycleVector R left right L
  let Y (n : ℕ) (R : Equiv.Perm (Fin n)) (k : Fin L) :=
    (totalCoreCount65 R left right k.val-totalCoefficient left right k.val*Real.log (n : ℝ))/
      Real.sqrt (totalCoefficient left right k.val*Real.log (n : ℝ))
  let Z (n : ℕ) (R : Equiv.Perm (Fin n)) (z : PowerIndex65 left right L) :=
    ((coreCategoryCount R (cornerCoreCategory65 z.1.val z.2.val) : ℝ)-
      cornerCoefficient z.1.val (cornerBehavior left right z.1.val) z.2.val*Real.log (n : ℝ))/
      Real.sqrt (cornerCoefficient z.1.val (cornerBehavior left right z.1.val) z.2.val*Real.log (n : ℝ))
  let a (s : ActiveCorner65 left right) (k : Fin L) := powerCornerWeight65 left right s k.val
  have ha (k : Fin L) : ∑ s, (a s k)^2 = 1 := powerCornerWeight_square_sum65 hp k.val
  have hZ := race_moments_characteristic65 w Z (power_core_target_moments65 f left right hp grid w hs L)
  have hY (t : Fin L → ℝ) : Tendsto (fun n => ∫ clocks,
      Complex.exp ((linearCombination65 t (Y n (raceRankPermutation clocks)) : ℂ)*I) ∂exponentialRace (w n))
      atTop (𝓝 (∫ z, Complex.exp ((linearCombination65 t z : ℂ)*I) ∂standardNormalVector (Fin L))) := by
    have hh := hZ (fun p => t p.2*a p.1 p.2)
    rw [gaussian_blocks_characteristic65 a ha t] at hh
    apply hh.congr'
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    have he (R : Equiv.Perm (Fin n)) : Y n R = fun k => ∑ s, a s k*Z n R (s,k) := by
      funext k
      exact totalCore_normalized_projection65 hp hn R k.val
    simp only [he,linearCombination_blocks65]
  have hXY (k : Fin L) : Tendsto (fun n => ∫ clocks,
      |X n (raceRankPermutation clocks) k-Y n (raceRankPermutation clocks) k| ∂exponentialRace (w n))
      atTop (𝓝 0) :=
    (totalCount_approx65 f left right hp grid w hs k.val).normalized (hp.totalCoefficient_pos65 k.val)
      (fun n => totalCoefficient left right k.val*Real.log (n : ℝ))
  apply race_characteristic_clt65 w X _ F
  intro t
  have hh := (race_characteristic_perturbation65 w X Y hXY t).add (hY t)
  simpa only [sub_add_cancel,zero_add] using hh

end Luce.Section6
