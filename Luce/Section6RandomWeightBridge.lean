import Luce.Section6WeightScaleConcentration
import Luce.Section5GapReservoir

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

theorem deleted_surviving_weight_antitone {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) :
    Antitone (fun t => ∑ i ∈ Finset.univ \ removed, w.rate i*clockSurvivalIndicator t i old) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : t < old i
  · have hs : s < old i := hst.trans_lt hi
    simp [clockSurvivalIndicator, hi, hs]
  · have hz : clockSurvivalIndicator t i old = 0 := by simp [clockSurvivalIndicator, hi]
    rw [hz, mul_zero]
    apply mul_nonneg (w.positive i).le
    rcases clockSurvivalIndicator_zero_one s i old with h | h <;> simp [h]

/-- Ordered remaining rate equals actual surviving weight at the start
of the gap, including the first-gap sentinel. -/
theorem raceGapRate_eq_surviving_weight {n : ℕ} (w : Weights n)
    (old : Fin n → ℝ) (hi : Function.Injective old) (hpos : ∀ i, 0 < old i) (q : Fin n) :
    raceGapRate w old q = ∑ i, w.rate i*clockSurvivalIndicator (raceGapStart old q) i old := by
  have ho : StrictMono (fun k => old (raceDraw old k)) := by
    rw [raceDraw_eq old hi]
    exact (drawPermutation_eq_iff_strictMono old hi _).mp rfl
  have h := orderedRemainingRate_eq_surviving_sum w (raceDraw old) old ho hpos q
  rw [raceGapRate, h]
  apply Finset.sum_congr rfl
  intro i _
  unfold clockSurvivalIndicator raceGapStart
  split_ifs <;> simp

/-- The same exact identity in the original undeleted labels. -/
theorem deleted_gap_rate_eq_surviving_weight {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (hi : Function.Injective old)
    (hpos : ∀ i, 0 < old i) (q : Fin (Finset.univ \ removed).card) :
    raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) q =
      ∑ i ∈ Finset.univ \ removed, w.rate i*
        clockSurvivalIndicator (raceGapStart (compactDeletedClocks removed old) q) i old := by
  rw [raceGapRate_eq_surviving_weight _ _ (compactDeletedClocks_injective removed old hi)
    (fun i => hpos (deletedClockLabel removed i)) q]
  rw [← sum_deletedClockLabel removed (fun i => w.rate i*
    clockSurvivalIndicator (raceGapStart (compactDeletedClocks removed old) q) i old)]
  rfl

/-- Endpoint control of a monotone surviving-weight path controls its
value at every intermediate, possibly random, time. -/
theorem deleted_weight_random_time_bound {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) {lo hi tau M err : ℝ}
    (hlo : lo ≤ tau) (hhi : tau ≤ hi)
    (hleft : |(∑ i ∈ Finset.univ \ removed, w.rate i*clockSurvivalIndicator lo i old)-M| ≤ err)
    (hright : |(∑ i ∈ Finset.univ \ removed, w.rate i*clockSurvivalIndicator hi i old)-M| ≤ err) :
    |(∑ i ∈ Finset.univ \ removed, w.rate i*clockSurvivalIndicator tau i old)-M| ≤ err := by
  have hl := deleted_surviving_weight_antitone w removed old hlo
  have hh := deleted_surviving_weight_antitone w removed old hhi
  rw [abs_le] at hleft hright ⊢
  exact ⟨by linarith only [hright.1, hh], by linarith only [hleft.2, hl]⟩

/-- Positivity and injectivity in the exact gap-rate identity are
discharged by the actual exponential race, not left as model inputs. -/
theorem deleted_gap_rate_eq_surviving_weight_ae {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card) :
    ∀ᵐ old ∂exponentialRace w,
      raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) q =
        ∑ i ∈ Finset.univ \ removed, w.rate i*
          clockSurvivalIndicator (raceGapStart (compactDeletedClocks removed old) q) i old := by
  filter_upwards [exponentialRace_injective_ae w, exponentialRace_positive_background w] with old hi hp
  exact deleted_gap_rate_eq_surviving_weight w removed old hi hp q

end Luce.Section6
