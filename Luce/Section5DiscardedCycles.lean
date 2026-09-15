import Luce.Section5RetainedExpectation
import Luce.Section5VertexCount

noncomputable section
open Function
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- A discarded root lies in the orbit of an excluded short-cycle vertex.
Charging the whole orbit costs at most its fixed length. -/
theorem deep_roots_le_retained_add_excluded {n : ℕ} (R : Equiv.Perm (Fin n))
    (k J : ℕ) (S : Finset (Fin n)) :
    ((deepShellLabels n J).filter (fun v => v ∈ Section5.maximumCycleRoots R k)).card ≤
      retainedDeepCycleCount R k S J +
        (k+1) * shortCycleVertexCount R (k+1) (Finset.univ \ S) := by
  let A := (deepShellLabels n J).filter (fun v => v ∈ Section5.maximumCycleRoots R k ∧
    (periodicOrbit (R : Fin n → Fin n) v).toFinset ⊆ S)
  let B := (Finset.univ \ S).filter (fun u => minimalPeriod (R : Fin n → Fin n) u ≤ k+1)
  let O := fun u => (periodicOrbit (R : Fin n → Fin n) u).toFinset
  have hsub : ((deepShellLabels n J).filter (fun v => v ∈ Section5.maximumCycleRoots R k)) ⊆
      A ∪ B.biUnion O := by
    intro v hv
    obtain ⟨hdeep, hroot⟩ := Finset.mem_filter.mp hv
    by_cases hretain : (periodicOrbit (R : Fin n → Fin n) v).toFinset ⊆ S
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hdeep, hroot, hretain⟩)
    · obtain ⟨u, hu, huS⟩ := Finset.not_subset.mp hretain
      have hvp := R.injective.mem_periodicPts v
      obtain ⟨m, hm⟩ := (mem_periodicOrbit_iff hvp).mp
        ((Section5.mem_periodicOrbit_toFinset R v u).mp hu)
      have hp : minimalPeriod (R : Fin n → Fin n) u = k+1 := by
        rw [← hm, minimalPeriod_apply_iterate hvp m]
        exact (Section5.mem_maximumCycleRoots_iff R k v).mp hroot |>.1
      have ho : periodicOrbit (R : Fin n → Fin n) u = periodicOrbit (R : Fin n → Fin n) v := by
        rw [← hm]
        exact periodicOrbit_apply_iterate_eq hvp m
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, huS⟩,
        hp.le⟩, ?_⟩
      dsimp [O]
      rw [ho, Section5.mem_periodicOrbit_toFinset]
      exact self_mem_periodicOrbit hvp
  have hcard : (B.biUnion O).card ≤ (k+1) * B.card := by
    calc
      _ ≤ ∑ u ∈ B, (O u).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ B, (k+1) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [show (O u).card = minimalPeriod (R : Fin n → Fin n) u from
          Section5.periodicOrbit_toFinset_card R u]
        exact (Finset.mem_filter.mp hu).2
      _ = _ := by simp [Nat.mul_comm]
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [shortCycleVertexCount_eq_filter_period_le]
  change _ ≤ A.card + (k+1)*B.card
  omega

theorem tail_cycles_le_retained_add_excluded {n : ℕ} (R : Equiv.Perm (Fin n))
    (k J : ℕ) (S : Finset (Fin n)) (α : ℝ)
    (hdeep : ∀ v : Fin n, α*n < (v.val : ℝ)+1 → J ≤ terminalShellNumber v) :
    Section5.cycleCount R k - Section5.bulkCycleCount R α k ≤
      retainedDeepCycleCount R k S J +
        (k+1)*shortCycleVertexCount R (k+1) (Finset.univ \ S) := by
  apply le_trans _ (deep_roots_le_retained_add_excluded R k J S)
  rw [Section5.tailCycleCount_eq_maximum_roots]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hroot, hvα⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdeep v hvα⟩, hroot⟩

end Luce
