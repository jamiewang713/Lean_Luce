import Luce.Section5DiscardedCycles
import Luce.Section5DiscardedLabels
import Luce.Section5FiniteStatistic
import Luce.Section5InteriorLowRates

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

theorem tail_cycle_expectation_le_retained_and_truncations (w : WeightArray)
    (n k J : ℕ) (M β δ α : ℝ)
    (hdeep : ∀ v : Fin n, α*n < (v.val : ℝ)+1 → J ≤ terminalShellNumber v) :
    (∫ e, ((Section5.cycleCount (raceRankPermutation e) k -
      Section5.bulkCycleCount (raceRankPermutation e) α k : ℕ) : ℝ)
      ∂exponentialRace (w n)) ≤
    (∫ e, (retainedDeepCycleCount (raceRankPermutation e) k
      (retainedCycleLabels (w n) M β δ) J : ℝ) ∂exponentialRace (w n)) +
    (k+1 : ℕ) * (highCycleExpectation w (k+1) n M +
      interiorLowCycleExpectation w (k+1) n β δ) := by
  let S := retainedCycleLabels (w n) M β δ
  let H := Finset.univ.filter (fun u => M < (w n).rate u)
  let L := Finset.univ.filter (fun u => (w n).rate u < δ ∧ (u.val : ℝ)+1 ≤ β*n)
  have hR := integrable_race_permutation_statistic (w n)
    (fun R => (retainedDeepCycleCount R k S J : ℝ))
  have hH := shortCycleVertexCount_integrable (w n) (k+1) H
  have hL := shortCycleVertexCount_integrable (w n) (k+1) L
  have hSum : Integrable (fun e => (shortCycleVertexCount (raceRankPermutation e) (k+1) H : ℝ) +
      (shortCycleVertexCount (raceRankPermutation e) (k+1) L : ℝ)) (exponentialRace (w n)) := hH.add hL
  have hScaled : Integrable (fun e => ((k+1 : ℕ) : ℝ) *
      ((shortCycleVertexCount (raceRankPermutation e) (k+1) H : ℝ) +
        (shortCycleVertexCount (raceRankPermutation e) (k+1) L : ℝ)))
      (exponentialRace (w n)) := hSum.const_mul _
  calc
    _ ≤ ∫ e, (retainedDeepCycleCount (raceRankPermutation e) k S J : ℝ) +
        (k+1 : ℕ) * ((shortCycleVertexCount (raceRankPermutation e) (k+1) H : ℝ) +
          (shortCycleVertexCount (raceRankPermutation e) (k+1) L : ℝ))
        ∂exponentialRace (w n) := by
      apply integral_mono (integrable_race_permutation_statistic (w n)
        (fun R => ((Section5.cycleCount R k - Section5.bulkCycleCount R α k : ℕ) : ℝ)))
        (hR.add hScaled)
      intro e
      have h := tail_cycles_le_retained_add_excluded (raceRankPermutation e) k J S α hdeep
      have hb := excluded_short_vertices_le_high_add_interior_low (w n)
        (raceRankPermutation e) (k+1) M β δ
      have hfinal := h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (k+1) hb) _)
      have hcast := (Nat.cast_le (α := ℝ)).mpr hfinal
      push_cast at hcast
      simpa only [Pi.add_apply, Nat.cast_add, Nat.cast_one, H, L] using hcast
    _ = _ := by
      rw [integral_add hR hScaled,
        integral_const_mul, integral_add hH hL]
      rfl

end Luce
