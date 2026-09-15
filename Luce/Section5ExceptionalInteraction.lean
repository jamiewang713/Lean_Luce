import Luce.Section5VertexCount

/-!
# Counting cycles which meet both exceptional sets

Source: `fixed_points.tex:1231–1237`. Each orbit of length at most L
contains at most L low vertices for each high vertex it contains. The
proof uses finite orbit unions, including singleton and empty cases.
-/

noncomputable section
open MeasureTheory Function Set
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Every vertex of the actual orbit avoids H. -/
def OrbitAvoids {n : ℕ} (R : Fin n → Fin n) (H : Finset (Fin n)) (v : Fin n) : Prop :=
  ∀ u ∈ periodicOrbit R v, u ∉ H

/-- Vertices in S in short cycles whose entire orbit avoids H. -/
def shortCycleVertexCountAvoiding {n : ℕ} (R : Fin n → Fin n)
    (L : ℕ) (S H : Finset (Fin n)) : ℕ :=
  (S.filter fun v => minimalPeriod R v ≤ L ∧ OrbitAvoids R H v).card

/-- Literal finite charging inequality in source 1231–1237. The sets
need not be disjoint; neither is required invariant under R. -/
theorem shortCycleVertexCount_le_high_add_avoiding {n : ℕ}
    (R : Equiv.Perm (Fin n)) (L : ℕ) (S H : Finset (Fin n)) :
    shortCycleVertexCount R L S ≤
      L * shortCycleVertexCount R L H + shortCycleVertexCountAvoiding R L S H := by
  let A := S.filter fun v => minimalPeriod (R : Fin n → Fin n) v ≤ L ∧ OrbitAvoids R H v
  let B := H.filter fun v => minimalPeriod (R : Fin n → Fin n) v ≤ L
  let O := fun v => (periodicOrbit (R : Fin n → Fin n) v).toFinset
  have hsub : (S.filter fun v => minimalPeriod (R : Fin n → Fin n) v ≤ L) ⊆
      A ∪ B.biUnion O := by
    intro v hv
    obtain ⟨hvS, hvL⟩ := Finset.mem_filter.mp hv
    by_cases ha : OrbitAvoids R H v
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvS, hvL, ha⟩)
    · have hex : ∃ u, u ∈ periodicOrbit (R : Fin n → Fin n) v ∧ u ∈ H := by
        simpa only [OrbitAvoids, not_forall, _root_.not_imp, not_not, exists_prop] using ha
      obtain ⟨u, hu, huH⟩ := hex
      have hvp := R.injective.mem_periodicPts v
      obtain ⟨m, hm⟩ := (mem_periodicOrbit_iff hvp).mp hu
      have hperiod : minimalPeriod (R : Fin n → Fin n) u =
          minimalPeriod (R : Fin n → Fin n) v := by
        rw [← hm]
        exact minimalPeriod_apply_iterate hvp m
      have horbit : periodicOrbit (R : Fin n → Fin n) u =
          periodicOrbit (R : Fin n → Fin n) v := by
        rw [← hm]
        exact periodicOrbit_apply_iterate_eq hvp m
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨u, Finset.mem_filter.mpr ⟨huH, hperiod ▸ hvL⟩, ?_⟩
      change v ∈ (periodicOrbit (R : Fin n → Fin n) u).toFinset
      rw [horbit, Section5.mem_periodicOrbit_toFinset]
      exact self_mem_periodicOrbit hvp
  have hbound : (B.biUnion O).card ≤ L * B.card := by
    calc
      _ ≤ ∑ u ∈ B, (O u).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ B, L := by
        apply Finset.sum_le_sum
        intro u hu
        rw [show (O u).card = minimalPeriod (R : Fin n → Fin n) u from
          Section5.periodicOrbit_toFinset_card R u]
        exact (Finset.mem_filter.mp hu).2
      _ = L * B.card := by simp [Nat.mul_comm]
  rw [shortCycleVertexCount_eq_filter_period_le,
    shortCycleVertexCount_eq_filter_period_le]
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (by
      change A.card + (B.biUnion O).card ≤ L * B.card + A.card
      omega))

lemma shortCycleVertexCountAvoiding_integrable {n : ℕ} (w : Weights n)
    (L : ℕ) (S H : Finset (Fin n)) :
    Integrable (fun clocks => (shortCycleVertexCountAvoiding
      (raceRankPermutation clocks) L S H : ℝ)) (exponentialRace w) := by
  apply Integrable.of_bound
    (((measurable_of_countable (fun R : Fin n → Fin n =>
      (shortCycleVertexCountAvoiding R L S H : ℝ))).comp
      measurable_raceRankPermutation_function).aestronglyMeasurable) (S.card : ℝ)
  apply Filter.Eventually.of_forall
  intro clocks
  change ‖(shortCycleVertexCountAvoiding (raceRankPermutation clocks) L S H : ℝ)‖ ≤ (S.card : ℝ)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast Finset.card_filter_le S _

/-- Integrating the finite orbit count is valid because both counts have
separately proved integrability. -/
theorem shortCycleVertexCount_expectation_le_high_add_avoiding {n : ℕ}
    (w : Weights n) (L : ℕ) (S H : Finset (Fin n)) :
    (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ)
      ∂exponentialRace w) ≤
      (L : ℝ) * (∫ clocks, (shortCycleVertexCount (raceRankPermutation clocks) L H : ℝ)
        ∂exponentialRace w) +
      ∫ clocks, (shortCycleVertexCountAvoiding (raceRankPermutation clocks) L S H : ℝ)
        ∂exponentialRace w := by
  rw [← integral_const_mul, ← integral_add
    ((shortCycleVertexCount_integrable w L H).const_mul _) (shortCycleVertexCountAvoiding_integrable w L S H)]
  apply integral_mono (shortCycleVertexCount_integrable w L S)
    (((shortCycleVertexCount_integrable w L H).const_mul _).add
      (shortCycleVertexCountAvoiding_integrable w L S H))
  intro clocks
  change (shortCycleVertexCount (raceRankPermutation clocks) L S : ℝ) ≤
    (L : ℝ) * shortCycleVertexCount (raceRankPermutation clocks) L H +
      shortCycleVertexCountAvoiding (raceRankPermutation clocks) L S H
  exact_mod_cast shortCycleVertexCount_le_high_add_avoiding (raceRankPermutation clocks) L S H

end Luce
