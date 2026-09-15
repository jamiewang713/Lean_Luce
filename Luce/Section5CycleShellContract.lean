import Luce.Section5ContractDefinitions
import Luce.Section5CycleCutoff
import Luce.Section5CycleProbability

/-! Independent closed contract for the manuscript's cycle-tail-tightness
proposition. The implementation and its auxiliary tail counts are not imported. -/
noncomputable section
open Luce MeasureTheory Filter
open scoped BigOperators Topology
namespace ShellMigrationContract

def cycleShell : Prop :=
  ∀ (w : WeightArray) (f : ℝ → ℝ), NormalizedWeights w → ProfileLimit w f →
    EndpointShellAssumption w → ∀ L : ℕ,
      Tendsto (fun α : ℝ => limsup (fun n : ℕ =>
        ∫ e, (∑ k : Fin L, (Section5.cycleCount (raceRankPermutation e) k.val -
          Section5.bulkCycleCount (raceRankPermutation e) α k.val : ℕ) : ℝ)
          ∂exponentialRace (w n)) atTop) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ))

end ShellMigrationContract
