import Luce.Section6RandomWeightBridge

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- Random-gap weight concentration from the two actual endpoint weight
events and the actual gap-time window. The only remaining helper premises
are deterministic bounds on the two deleted means. -/
theorem random_gap_weight_probability_bound {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card)
    {lo hi M eps drift : ℝ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (heps : 0 < eps)
    (hmeanlo : |(n : ℝ)*deletedD w removed 1 lo-M| ≤ drift)
    (hmeanhi : |(n : ℝ)*deletedD w removed 1 hi-M| ≤ drift) :
    (exponentialRace w).real {old | eps+drift <
      |raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) q-M|} ≤
      (exponentialRace w).real {old | raceGapStart (compactDeletedClocks removed old) q < lo} +
      (exponentialRace w).real {old | hi < raceGapStart (compactDeletedClocks removed old) q} +
      ((n : ℝ)*deletedD w removed 2 lo + (n : ℝ)*deletedD w removed 2 hi)/eps^2 := by
  let A := {old | raceGapStart (compactDeletedClocks removed old) q < lo}
  let B := {old | hi < raceGapStart (compactDeletedClocks removed old) q}
  let C := {old : Fin n → ℝ | eps ≤ |(∑ i ∈ Finset.univ \ removed,
    w.rate i*clockSurvivalIndicator lo i old)-(n : ℝ)*deletedD w removed 1 lo|}
  let D := {old : Fin n → ℝ | eps ≤ |(∑ i ∈ Finset.univ \ removed,
    w.rate i*clockSurvivalIndicator hi i old)-(n : ℝ)*deletedD w removed 1 hi|}
  have hinc : ∀ᵐ old ∂exponentialRace w, eps+drift <
      |raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) q-M| →
      old ∈ (A ∪ B) ∪ (C ∪ D) := by
    filter_upwards [deleted_gap_rate_eq_surviving_weight_ae w removed q] with old heq
    intro hbad
    by_contra hgood
    simp only [A, B, C, D, Set.mem_union, Set.mem_ofPred_eq, not_or] at hgood
    have hl : |(∑ i ∈ Finset.univ \ removed, w.rate i*clockSurvivalIndicator lo i old)-M| ≤ eps+drift :=
      (abs_sub_le _ ((n : ℝ)*deletedD w removed 1 lo) _).trans
        (add_le_add (lt_of_not_ge hgood.2.1).le hmeanlo)
    have hh : |(∑ i ∈ Finset.univ \ removed, w.rate i*clockSurvivalIndicator hi i old)-M| ≤ eps+drift :=
      (abs_sub_le _ ((n : ℝ)*deletedD w removed 1 hi) _).trans
        (add_le_add (lt_of_not_ge hgood.2.2).le hmeanhi)
    have hb := deleted_weight_random_time_bound w removed old
      (le_of_not_gt hgood.1.1) (le_of_not_gt hgood.1.2) hl hh
    rw [heq] at hbad
    exact (not_lt_of_ge hb) hbad
  have hC := deleted_remaining_weight_chebyshev w hn removed hlo heps
  have hD := deleted_remaining_weight_chebyshev w hn removed hhi heps
  calc
    _ ≤ (exponentialRace w).real ((A ∪ B) ∪ (C ∪ D)) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hinc)
    _ ≤ (exponentialRace w).real (A ∪ B)+(exponentialRace w).real (C ∪ D) :=
      measureReal_union_le _ _
    _ ≤ ((exponentialRace w).real A+(exponentialRace w).real B)+
        ((exponentialRace w).real C+(exponentialRace w).real D) :=
      add_le_add (measureReal_union_le _ _) (measureReal_union_le _ _)
    _ ≤ ((exponentialRace w).real A+(exponentialRace w).real B)+
        ((n : ℝ)*deletedD w removed 2 lo/eps^2+(n : ℝ)*deletedD w removed 2 hi/eps^2) :=
      add_le_add le_rfl (add_le_add hC hD)
    _ = _ := by rw [add_div]

end Luce.Section6
