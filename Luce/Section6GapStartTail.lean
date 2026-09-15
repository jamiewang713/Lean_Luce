import Luce.Section6ArrivalConcentration

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- If the start of gap q is before t, at least q clocks are before t.
The initial gap is included and needs no positivity assumption on t. -/
theorem gapStart_lt_imp_beforeCount {n : ℕ} (old : Fin n → ℝ)
    (hi : Function.Injective old) (q : Fin n) {t : ℝ}
    (hs : raceGapStart old q < t) : q.val ≤ clockBeforeCount old t := by
  rw [raceGapStart_eq_consecutiveGapLower old hi] at hs
  unfold consecutiveGapLower at hs
  split_ifs at hs with hq
  · omega
  · have hb := (arrivalTime_lt_iff_clockBeforeCount old hi ⟨q.val-1, by omega⟩ t).mp hs
    simp only [Fin.val_mk] at hb
    omega

/-- Concrete deleted gap-start lower tail from an arrival-mean bound.
This is a finite helper; endpoint mean estimates still must discharge hmean. -/
theorem deleted_gap_start_tail_of_arrival_mean {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card)
    {t : ℝ} (ht : 0 ≤ t) (hmean : (n : ℝ)*deletedG w removed t ≤ (q.val : ℝ)/2) :
    (exponentialRace w).real {old | raceGapStart (compactDeletedClocks removed old) q < t} ≤
      Real.exp (-((Real.log 2-1/2)*(q.val : ℝ))) := by
  apply le_trans _ (deleted_before_count_upper_tail w hn removed ht hmean)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [exponentialRace_injective_ae w] with old hi
  intro hs
  have hb := gapStart_lt_imp_beforeCount (compactDeletedClocks removed old)
    (compactDeletedClocks_injective removed old hi) q hs
  rw [clockBeforeCount_compactDeletedClocks] at hb
  exact_mod_cast hb

end Luce.Section6
