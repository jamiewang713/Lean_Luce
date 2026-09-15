import Luce.Section65SpatialCategories
import Luce.Section65SpatialCoreComparison
import Luce.Section65CountApproximation
import Luce.Section65CharacteristicPerturbation

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology BigOperators BoundedContinuousFunction
namespace Luce.Section6

theorem spatialCount_approx65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (side : Corner) (ha : (cornerBehavior left right side).active) (k : ℕ) {a b : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) :
    CountApprox65 w (fun _ R => (spatialCycleCount R side k a b : ℝ))
      (fun _ R => (coreCategoryCount R (spatialCoreCategory65 side k a b) : ℝ)) := by
  obtain ⟨C,hC,h⟩ := spatialCore_error_bound65 f left right hp grid w hs side ha k ha0 hab hb1
  exact countApprox65_of_const_bound w _ _ hC.le h

theorem spatialCount_meanApprox65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (side : Corner) (ha : (cornerBehavior left right side).active) (k : ℕ) {a b : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) :
    MeanApprox65 (fun n => ∫ clocks, (spatialCycleCount (raceRankPermutation clocks) side k a b : ℝ)
      ∂exponentialRace (w n)) (cornerCoefficient side (cornerBehavior left right side) k*(b-a)) :=
  (spatialCount_approx65 f left right hp grid w hs side ha k ha0 hab hb1).mean
    (coreCount_meanApprox65 f left right hp grid w hs (spatialCoreCategory65 side k a b) ha
      (idealSpatialTrace_meanApprox65 f left right hp side ha k ha0 hab hb1))

theorem spatial_race_clt65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (L J : ℕ) (a b : Fin J → ℝ)
    (hab : ∀ j, 0 < a j ∧ a j < b j ∧ b j < 1)
    (hd : Pairwise fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))
    (F : (SpatialIndex left right L J → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ clocks,
      F (normalizedSpatialVector (raceRankPermutation clocks) left right L J a b) ∂exponentialRace (w n))
      atTop (𝓝 (∫ z, F z ∂standardNormalVector (SpatialIndex left right L J))) := by
  classical
  let X (n : ℕ) (R : Equiv.Perm (Fin n)) := normalizedSpatialVector R left right L J a b
  let Y (n : ℕ) (R : Equiv.Perm (Fin n)) (z : SpatialIndex left right L J) :=
    ((coreCategoryCount R (spatialCategory65 a b z) : ℝ)-spatialCoefficient65 a b z*Real.log (n : ℝ))/
      Real.sqrt (spatialCoefficient65 a b z*Real.log (n : ℝ))
  have hY := race_moments_characteristic65 w Y (spatial_core_target_moments65 f left right hp grid w hs L J a b hab hd)
  have hXY (z : SpatialIndex left right L J) : Tendsto (fun n => ∫ clocks,
      |X n (raceRankPermutation clocks) z-Y n (raceRankPermutation clocks) z| ∂exponentialRace (w n))
      atTop (𝓝 0) := by
    exact (spatialCount_approx65 f left right hp grid w hs z.1.val z.1.property z.2.1.val
      (hab z.2.2).1 (hab z.2.2).2.1 (hab z.2.2).2.2).normalized
      (mul_pos (hp.cornerCoefficient_pos65 _ z.1.property _) (sub_pos.mpr (hab z.2.2).2.1))
      (fun n => spatialCoefficient65 a b z*Real.log (n : ℝ))
  apply race_characteristic_clt65 w X _ F
  intro t
  have hh := (race_characteristic_perturbation65 w X Y hXY t).add (hY t)
  simpa only [sub_add_cancel,zero_add] using hh

end Luce.Section6
