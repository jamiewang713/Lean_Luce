import Luce.Section65TotalCoreExpectation
import Luce.Section65IdealMean

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Luce.Section6

theorem totalCore_meanApprox65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (k : ℕ) : MeanApprox65 (fun n => ∫ clocks,
      totalCoreCount65 (raceRankPermutation clocks) left right k ∂exponentialRace (w n))
        (totalCoefficient left right k) := by
  have hh (s : ActiveCorner65 left right) := coreCount_meanApprox65 f left right hp grid w hs
    (cornerCoreCategory65 s.val k) s.property (idealTrace_meanApprox65 f left right hp s.val s.property k)
  have ht := tendsto_finsetSum Finset.univ (fun s (_ : s ∈ (Finset.univ : Finset (ActiveCorner65 left right))) => hh s)
  simp only [Finset.sum_const_zero] at ht
  unfold MeanApprox65
  convert ht using 1
  funext n
  dsimp only [totalCoreCount65]
  rw [race_integral_sum65 (w n)
    (fun (s : ActiveCorner65 left right) R => (coreCategoryCount R (cornerCoreCategory65 s.val k) : ℝ))]
  simp only [← Finset.sum_div,Finset.sum_sub_distrib,← Finset.sum_mul,sum_active_coefficients65]

theorem cycleCount_meanApprox65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (k : ℕ) : MeanApprox65 (fun n => ∫ clocks, (Section5.cycleCount (raceRankPermutation clocks) k : ℝ)
      ∂exponentialRace (w n)) (totalCoefficient left right k) :=
  (totalCount_approx65 f left right hp grid w hs k).mean (totalCore_meanApprox65 f left right hp grid w hs k)

theorem MeanApprox65.ratio_one {μ : ℕ → ℝ} {β : ℝ} (h : MeanApprox65 μ β) (hβ : β ≠ 0) :
    Tendsto (fun n => μ n/(β*Real.log (n : ℝ))) atTop (𝓝 1) := by
  have hh := h.ratio.div_const β
  rw [div_self hβ] at hh
  simpa only [div_div,mul_comm] using hh

end Luce.Section6
