import Luce.Section6Lemma64Contract
import Luce.Section6ActiveCycleBounds

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- The complete cycle-count portion of the independently frozen contract.
There are no parameters outside the closed proposition. -/
theorem lemma64_cycles : Lemma64Contract.cycles := by
  classical
  intro f left right hp grid w hw k
  choose R D hR hD hD1 hroot using hp.active_root_bounds k
  choose E F hE hF hF1 hdiscard using hp.active_discarded_bounds k
  let delta := min (min (D .left) (D .right)) (min (F .left) (F .right))
  have hd : 0 < delta := lt_min (lt_min (hD .left) (hD .right)) (lt_min (hF .left) (hF .right))
  have hdR (side : Corner) : delta ≤ D side := by
    cases side
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
  have hdE (side : Corner) : delta ≤ F side := by
    cases side
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hd1 : delta < 1 := (hdR .left).trans_lt (hD1 .left)
  obtain ⟨I, hI, hinterior⟩ := hp.interior_maximum_root_expectation hd k
  let C := I + R .left + R .right + E .left + E .right
  have hrL := hR .left
  have hrR := hR .right
  have heL := hE .left
  have heR := hE .right
  have hC : 0 < C := by dsimp [C]; positivity
  have hIC : I ≤ C := by dsimp [C]; linarith
  have hRC (side : Corner) : R side ≤ C := by cases side <;> dsimp [C] <;> linarith
  have hEC (side : Corner) : E side ≤ C := by cases side <;> dsimp [C] <;> linarith
  have he (n : ℕ) (v : Fin n) :
      (∫ clocks, ((Finset.univ.filter (fun c : ↥(Section5.cycleOrbits (raceRankPermutation clocks) k) =>
        Section5.cycleMaximum (raceRankPermutation clocks) k c = v)).card : ℝ)
        ∂exponentialRace (w n)) =
      ∫ clocks, (if v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k then (1 : ℝ) else 0)
        ∂exponentialRace (w n) := by
    apply integral_congr_ae
    filter_upwards [] with clocks
    exact_mod_cast cycle_count_at_maximum_eq_indicator (raceRankPermutation clocks) k v
  refine ⟨C, delta, hC, hd, hd1, ?_, ?_⟩
  · intro n v hl hu
    rw [he]
    exact (hinterior grid w hw n v hl hu).trans
      (div_le_div_of_nonneg_right hIC (Nat.cast_nonneg _))
  · intro side hactive
    constructor
    · intro n v hv
      rw [he]
      exact (hroot side hactive grid w hw n v (hv.trans (hdR side))).trans
        (div_le_div_of_nonneg_right (hRC side) (Nat.cast_nonneg _))
    · intro n A B hB
      exact (hdiscard side hactive grid w hw n A B (hB.trans (hdE side))).trans (hEC side)

end Luce.Section6
