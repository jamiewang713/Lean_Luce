import Luce.Section6CriticalBlocks
import Luce.Section6FilteredCycleCount
import Luce.Section5MaximumCylinder

noncomputable section
open MeasureTheory Function
open scoped BigOperators
namespace Luce.Section6

theorem critical_cycle_count_complement {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (S : Finset (Fin n)) :
    Section5.cycleCount R k ≤ Section5.cycleCountWithin R S k+
      exactCycleVertexCount R (k+1) (Finset.univ \ S) := by
  classical
  let T := (Section5.cycleOrbits R k).filter (fun c => ¬c.toFinset ⊆ S)
  let V := (Finset.univ \ S).filter (fun i => minimalPeriod (R : Fin n → Fin n) i = k+1)
  have hsub : T ⊆ V.image (periodicOrbit (R : Fin n → Fin n)) := by
    intro c hc
    obtain ⟨hck,hout⟩ := Finset.mem_filter.mp hc
    obtain ⟨i,hic,hiS⟩ := Finset.not_subset.mp hout
    refine Finset.mem_image.mpr ⟨i,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hiS⟩,
        Section5.minimalPeriod_of_mem_cycleOrbit R k c hck i hic⟩
    · exact Section5.periodicOrbit_eq_of_mem_cycleOrbit R k c hck i hic
  have hbad : T.card ≤ V.card := (Finset.card_le_card hsub).trans Finset.card_image_le
  have hpartition := Finset.card_filter_add_card_filter_not (s := Section5.cycleOrbits R k)
    (p := fun c => c.toFinset ⊆ S)
  change _ + T.card = Section5.cycleCount R k at hpartition
  change _ ≤ ((Section5.cycleOrbits R k).filter (fun c => c.toFinset ⊆ S)).card+V.card
  omega

theorem critical_cycle_count_split {n : ℕ} (R : Equiv.Perm (Fin n)) (k M B : ℕ) :
    Section5.cycleCount R k ≤ Section5.cycleCountWithin R (criticalBlock n M B) k+M+
      exactCycleVertexCount R (k+1) (criticalBlock n (B+1) n) := by
  classical
  let E : Finset (Fin n) := Finset.univ.filter (fun i => i.val < M)
  let V := (criticalBlock n (B+1) n).filter (fun i => minimalPeriod (R : Fin n → Fin n) i = k+1)
  have hE : E.card ≤ M := by
    have hsub : E.image Fin.val ⊆ Finset.range M := by
      rintro i hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    have hh := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective,Finset.card_range] at hh
    exact hh
  have hsub : ((Finset.univ \ criticalBlock n M B).filter
      (fun i => minimalPeriod (R : Fin n → Fin n) i = k+1)) ⊆ E ∪ V := by
    intro i hi
    obtain ⟨hiS,hperiod⟩ := Finset.mem_filter.mp hi
    have hh := (Finset.mem_sdiff.mp hiS).2
    by_cases hlow : i.val < M
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlow⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,i.isLt⟩,hperiod⟩
      have hnot : ¬(M ≤ i.val+1 ∧ i.val+1 ≤ B) := by
        simpa only [criticalBlock,Finset.mem_filter,Finset.mem_univ,true_and] using hh
      omega
  have hv := (Finset.card_le_card hsub).trans (Finset.card_union_le E V)
  have hh := critical_cycle_count_complement R k (criticalBlock n M B)
  change _ ≤ _+((Finset.univ \ criticalBlock n M B).filter
      (fun i => minimalPeriod (R : Fin n → Fin n) i = k+1)).card at hh
  change _ ≤ _+M+V.card
  omega

theorem critical_retained_count_eq_subtype {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (S : Finset (Fin n)) :
    Section5.cycleCountWithin R S k =
      (Finset.univ.filter (fun c : ↥(Section5.cycleOrbits R k) => c.val.toFinset ⊆ S)).card := by
  classical
  unfold Section5.cycleCountWithin Section5.cycleOrbitsWithin
  exact Finset.card_bij (fun c hc => (⟨c,(Finset.mem_filter.mp hc).1⟩ : ↥(Section5.cycleOrbits R k)))
    (by intro c hc; simpa using (Finset.mem_filter.mp hc).2)
    (by intro c hc d hd h; exact congrArg Subtype.val h)
    (by intro c hc; exact ⟨c.val,Finset.mem_filter.mpr ⟨c.property,(Finset.mem_filter.mp hc).2⟩,rfl⟩)

theorem critical_retained_expectation {n : ℕ} (w : Weights n) (k : ℕ) (S : Finset (Fin n)) :
    (∫ e, (Section5.cycleCountWithin (raceRankPermutation e) S k : ℝ) ∂exponentialRace w) =
      ∑ v, (exponentialRace w).real (retainedMaximumCycleEvent k S v) := by
  classical
  simp_rw [critical_retained_count_eq_subtype]
  have hh := filtered_cycle_expectation_eq_probability_sum w k (fun _ c => c.toFinset ⊆ S)
  have hr : (∑ v : Fin n, (exponentialRace w).real {e |
      v ∈ Section5.maximumCycleRoots (raceRankPermutation e) k ∧
        (periodicOrbit (raceRankPermutation e : Fin n → Fin n) v).toFinset ⊆ S}) =
      ∑ v, (exponentialRace w).real (retainedMaximumCycleEvent k S v) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [retainedMaximumCycleEvent_eq_actual_roots]
  convert hh.trans hr using 1
  congr 1
  funext e
  congr 2
  ext c
  simp

end Luce.Section6
