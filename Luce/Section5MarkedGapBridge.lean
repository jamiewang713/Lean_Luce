import Luce.Section5DeletedGaps
import Luce.Section5GapTaylor
import Luce.Section5GapLaw
import Luce.Section5DeletedRace

/-!
# Exact endpoints and empirical values for marked insertion gaps

This file connects the exact deleted-clock kernel to the finite gap mass
used in the Taylor estimate. It also records the empirical CDF at both
endpoints, normalized by the original row size, not the deleted row size.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

lemma sum_deletedClockLabel {n : ℕ} (removed : Finset (Fin n)) (g : Fin n → ℝ) :
    (∑ k, g (deletedClockLabel removed k)) = ∑ i ∈ Finset.univ \ removed, g i := by
  exact ((Finset.univ \ removed).equivFin.symm.sum_comp (fun i => g i.val)).trans
    (Finset.sum_coe_sort _ g)

lemma consecutiveGapLower_eq_previous {m : ℕ} (times : Fin m → ℝ)
    (htimes : Injective times) (q : Fin m) :
    consecutiveGapLower times htimes q =
      previousOrderedTime (fun k => times (drawPermutation times htimes k)) q := by
  unfold consecutiveGapLower previousOrderedTime
  split_ifs <;> rfl

lemma consecutiveGapLower_le_upper {m : ℕ} (times : Fin m → ℝ)
    (htimes : Injective times) (hpos : ∀ i, 0 ≤ times i) (q : Fin m) :
    consecutiveGapLower times htimes q ≤ arrivalTime times htimes q := by
  unfold consecutiveGapLower
  split_ifs with hq
  · exact hpos _
  · exact (draw_arrivalTime_le_iff times htimes ⟨q.val - 1, by omega⟩ q).mpr (by
      change q.val - 1 ≤ q.val
      omega)

/-- The exact kernel is the actual exponential mass of this consecutive
gap; the duration is proved nonnegative before applying Taylor estimates. -/
theorem deletedGapKernel_toReal_eq_exponentialGapMass {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (hold : Injective old)
    (hpos : ∀ i, 0 ≤ old i) (i : Fin n) (q : Fin (Finset.univ \ removed).card) :
    (deletedGapKernel w removed old i q.val).toReal =
      exponentialGapMass (w.rate i)
        (consecutiveGapLower (compactDeletedClocks removed old)
          (compactDeletedClocks_injective removed old hold) q)
        (arrivalTime (compactDeletedClocks removed old)
            (compactDeletedClocks_injective removed old hold) q -
          consecutiveGapLower (compactDeletedClocks removed old)
            (compactDeletedClocks_injective removed old hold) q) := by
  rw [deletedGapKernel_eq_interval_measure w removed old hold hpos i q]
  have hlow := consecutiveGapLower_nonneg (compactDeletedClocks removed old)
    (compactDeletedClocks_injective removed old hold) (fun k => hpos _) q
  have hlen := sub_nonneg.mpr (consecutiveGapLower_le_upper (compactDeletedClocks removed old)
    (compactDeletedClocks_injective removed old hold) (fun k => hpos _) q)
  have h := exponentialGapMass_eq_measure (w.positive i) hlow hlen
  simpa only [add_sub_cancel, Measure.real] using h

/-- The deleted CDF at the upper endpoint T_(q+1) is `(q+1)/n` with
the original row-size normalization. -/
theorem deletedEmpiricalArrival_gapUpper {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (hold : Injective old) (q : Fin (Finset.univ \ removed).card) :
    deletedEmpiricalArrival removed old
      (arrivalTime (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold) q) = ((q.val : ℝ) + 1) / n := by
  let times := compactDeletedClocks removed old
  let ht := compactDeletedClocks_injective removed old hold
  change (∑ i ∈ Finset.univ \ removed, arrivalAt (arrivalTime times ht q) (old i)) / n = _
  rw [← sum_deletedClockLabel removed (fun i => arrivalAt (arrivalTime times ht q) (old i))]
  change (∑ k, arrivalAt (arrivalTime times ht q) (times k)) / n = _
  rw [← Equiv.sum_comp (drawPermutation times ht)
    (fun i => arrivalAt (arrivalTime times ht q) (times i))]
  simp_rw [arrivalAt, draw_arrivalTime_le_iff times ht]
  rw [Finset.sum_boole]
  have hs : (Finset.univ.filter fun k : Fin (Finset.univ \ removed).card => k ≤ q) = Finset.Iic q := by
    ext k
    simp
  rw [hs, Fin.card_Iic]
  simp

/-- The deleted CDF at the lower endpoint T_q is exactly `q/n`.
Strict positivity handles T₀=0 without an extra initial atom. -/
theorem deletedEmpiricalArrival_gapLower {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (hold : Injective old) (hpos : ∀ i, 0 < old i)
    (q : Fin (Finset.univ \ removed).card) :
    deletedEmpiricalArrival removed old
      (consecutiveGapLower (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold) q) = (q.val : ℝ) / n := by
  unfold consecutiveGapLower
  split_ifs with hq
  · simp only [deletedEmpiricalArrival, arrivalAt,
      show ∀ i, ¬old i ≤ 0 from fun i => not_le_of_gt (hpos i), if_false,
      Finset.sum_const_zero, zero_div, hq, Nat.cast_zero]
  · rw [deletedEmpiricalArrival_gapUpper removed old hold]
    congr 1
    push_cast
    have hn : 1 ≤ q.val := by omega
    norm_cast
    omega

/-- The normalized gap variable is the actual rate times the exact finite
gap duration used above. This fixes the zero-based gap orientation. -/
theorem orderedNormalizedGaps_compactDeleted {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (hold : Injective old)
    (q : Fin (Finset.univ \ removed).card) :
    orderedNormalizedGaps (compactDeletedWeights w removed)
      (drawPermutation (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold))
      (compactDeletedClocks removed old) q =
      orderedRemainingRate (compactDeletedWeights w removed)
        (drawPermutation (compactDeletedClocks removed old)
          (compactDeletedClocks_injective removed old hold)) q *
        (arrivalTime (compactDeletedClocks removed old)
            (compactDeletedClocks_injective removed old hold) q -
          consecutiveGapLower (compactDeletedClocks removed old)
            (compactDeletedClocks_injective removed old hold) q) := by
  rw [orderedNormalizedGaps_eq_rate_mul_gap, consecutiveGapLower_eq_previous]
  rfl

lemma arrivalTime_strictMono {m : ℕ} (times : Fin m → ℝ) (htimes : Injective times) :
    StrictMono (arrivalTime times htimes) := by
  intro a b hab
  have hle := (draw_arrivalTime_le_iff times htimes a b).mpr hab.le
  exact lt_of_le_of_ne hle (fun h => hab.ne ((drawPermutation times htimes).injective (htimes h)))

/-- Just after T_q the unmarked strict-survival rate is exactly W_q.
The denominator remains the original n, as required by the deleted race LLN. -/
theorem deletedEmpiricalRemaining_gapLower {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (hold : Injective old)
    (hpos : ∀ i, 0 < old i) (q : Fin (Finset.univ \ removed).card) :
    deletedEmpiricalRemaining w removed old
      (consecutiveGapLower (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold) q) =
      orderedRemainingRate (compactDeletedWeights w removed)
        (drawPermutation (compactDeletedClocks removed old)
          (compactDeletedClocks_injective removed old hold)) q / n := by
  rw [orderedRemainingRate_eq_surviving_sum _ _ _
    (arrivalTime_strictMono _ (compactDeletedClocks_injective removed old hold))
    (fun k => hpos _), ← consecutiveGapLower_eq_previous]
  unfold deletedEmpiricalRemaining
  congr 1
  symm
  exact sum_deletedClockLabel removed (fun i =>
    if consecutiveGapLower (compactDeletedClocks removed old)
      (compactDeletedClocks_injective removed old hold) q < old i then w.rate i else 0)

end Luce
