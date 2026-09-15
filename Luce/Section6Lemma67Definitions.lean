import Luce.Section6DiscardedCountDefinitions
import Luce.Section5CycleProbability

noncomputable section
open Function
namespace Luce.Section6

/-- Literal unrooted cycles, selected by their unique largest-label root. -/
def selectedRootCycleCount {n : ℕ} (p : Equiv.Perm (Fin n)) (k : ℕ)
    (S : Finset (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter fun c : ↥(Section5.cycleOrbits p k) =>
    Section5.cycleMaximum p k c ∈ S).card

/-- Root depths are in the closed real interval [A,B]. The distance
threshold is non-strict, exactly as in Lemma 6.7, including R=1. -/
def logarithmicExcursionCount {n : ℕ} (p : Equiv.Perm (Fin n))
    (side : Corner) (k : ℕ) (A B R : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun c : ↥(Section5.cycleOrbits p k) =>
    A ≤ (cornerDistance side (Section5.cycleMaximum p k c) : ℝ) ∧
    (cornerDistance side (Section5.cycleMaximum p k c) : ℝ) ≤ B ∧
    ∃ v ∈ c.val.toFinset,
      Real.log R ≤ |Real.log (cornerDistance side v) -
        Real.log (cornerDistance side (Section5.cycleMaximum p k c))|).card

def rootLogExcursionEvent {n : ℕ} (side : Corner) (k : ℕ) (v : Fin n) (R : ℝ) :
    Set (Fin n → ℝ) :=
  {clocks | v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k ∧
    ∃ z ∈ (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v).toFinset,
      Real.log R ≤ |Real.log (cornerDistance side z) - Real.log (cornerDistance side v)|}

/-- All labels separated from the active corners. There is no restriction
at an inactive corner. These sets include every fixed middle interval and
a fixed neighborhood of each inactive endpoint. -/
def offActiveLabels (left right : EndpointBehavior) (n : ℕ) (eps : ℝ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i =>
    (left.active → eps ≤ ((i.val : ℝ)+1)/(n : ℝ)) ∧
    (right.active → eps ≤ (cornerDistance .right i : ℝ)/(n : ℝ))

end Luce.Section6
