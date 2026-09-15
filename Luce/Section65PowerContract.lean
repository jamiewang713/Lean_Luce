import Luce.Section65PowerLimit
import Luce.Section65PowerMean
import Luce.Section65LuceTransfer
import Luce.Section6Contract

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
universe u
namespace Luce.Section6

theorem powerLaw65 (grid : SamplingGrid) : SampledProfileContract.powerLaw.{u} grid := by
  intro Ω mΩ P hP
  letI : ∀ n, MeasurableSpace (Ω n) := mΩ
  letI : ∀ n, IsProbabilityMeasure (P n) := hP
  intro w f left right hs hp π hπ hmass
  constructor
  · intro k
    refine ⟨hp.totalCoefficient_pos65 k,?_⟩
    have hh := (cycleCount_meanApprox65 f left right hp grid w hs k).ratio_one (hp.totalCoefficient_pos65 k).ne'
    have he (n : ℕ) : (∫ ω, (Section5.cycleCount (π n ω) k : ℝ) ∂P n) =
        ∫ clocks, (Section5.cycleCount (raceRankPermutation clocks) k : ℝ) ∂exponentialRace (w n) :=
      luce_invariant_integral_eq65 (P n) (w n) (π n) (hπ n) (hmass n)
        (fun R => (Section5.cycleCount R k : ℝ)) (fun R => by simp only [Section5.cycleCount_symm])
    simpa only [he] using hh
  · intro L F
    have hh := power_race_clt65 f left right hp grid w hs L F
    have he (n : ℕ) : (∫ ω, F (normalizedCycleVector (π n ω) left right L) ∂P n) =
        ∫ clocks, F (normalizedCycleVector (raceRankPermutation clocks) left right L) ∂exponentialRace (w n) := by
      apply luce_invariant_integral_eq65 (P n) (w n) (π n) (hπ n) (hmass n)
        (fun R => F (normalizedCycleVector R left right L))
      intro R
      congr 1
      funext k
      simp only [normalizedCycleVector,Section5.cycleCount_symm]
    simpa only [he] using hh

end Luce.Section6
