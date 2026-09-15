import Luce.Section65SpatialLimit
import Luce.Section65Localization
import Luce.Section65LuceTransfer
import Luce.Section6Contract

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
universe u
namespace Luce.Section6

theorem spatial65 (grid : SamplingGrid) : SampledProfileContract.spatial.{u} grid := by
  intro Ω mΩ P hP
  letI : ∀ n, MeasurableSpace (Ω n) := mΩ
  letI : ∀ n, IsProbabilityMeasure (P n) := hP
  intro w f left right hs hp π hπ hmass L J a b hab hd
  refine ⟨?_,?_,?_⟩
  · intro z
    refine ⟨hp.cornerCoefficient_pos65 _ z.1.property _,?_⟩
    have hh := (spatialCount_meanApprox65 f left right hp grid w hs z.1.val z.1.property z.2.1.val
      (hab z.2.2).1 (hab z.2.2).2.1 (hab z.2.2).2.2).ratio
    have he (n : ℕ) : (∫ ω, (spatialCycleCount (π n ω) z.1.val z.2.1.val (a z.2.2) (b z.2.2) : ℝ) ∂P n) =
        ∫ clocks, (spatialCycleCount (raceRankPermutation clocks) z.1.val z.2.1.val (a z.2.2) (b z.2.2) : ℝ)
          ∂exponentialRace (w n) :=
      luce_invariant_integral_eq65 (P n) (w n) (π n) (hπ n) (hmass n)
        (fun R => (spatialCycleCount R z.1.val z.2.1.val (a z.2.2) (b z.2.2) : ℝ))
        (fun R => by rw [spatialCycleCount_symm65])
    simpa only [he] using hh
  · intro F
    have hh := spatial_race_clt65 f left right hp grid w hs L J a b hab hd F
    have he (n : ℕ) : (∫ ω, F (normalizedSpatialVector (π n ω) left right L J a b) ∂P n) =
        ∫ clocks, F (normalizedSpatialVector (raceRankPermutation clocks) left right L J a b)
          ∂exponentialRace (w n) := by
      apply luce_invariant_integral_eq65 (P n) (w n) (π n) (hπ n) (hmass n)
        (fun R => F (normalizedSpatialVector R left right L J a b))
      intro R
      congr 1
      funext z
      simp only [normalizedSpatialVector,spatialCycleCount_symm65]
    simpa only [he] using hh
  · intro z δ hδ
    have hh := localization65 f left right hp grid w hs z.1.val z.1.property z.2.1.val
      (hab z.2.2).1 (hab z.2.2).2.1 (hab z.2.2).2.2 hδ
    have he (n : ℕ) : (∫ ω, (excursionCycleCount (π n ω) z.1.val z.2.1.val (a z.2.2) (b z.2.2) δ : ℝ) ∂P n) =
        ∫ clocks, (excursionCycleCount (raceRankPermutation clocks) z.1.val z.2.1.val (a z.2.2) (b z.2.2) δ : ℝ)
          ∂exponentialRace (w n) :=
      luce_invariant_integral_eq65 (P n) (w n) (π n) (hπ n) (hmass n)
        (fun R => (excursionCycleCount R z.1.val z.2.1.val (a z.2.2) (b z.2.2) δ : ℝ))
        (fun R => by rw [excursionCycleCount_symm65])
    simpa only [he] using hh

end Luce.Section6
