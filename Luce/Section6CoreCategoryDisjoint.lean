import Luce.Section6CoreCategoryDefinitions
import Luce.Section6CategoryFactorialExpectation

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem opposite_core_sets_disjoint {n A B : ℕ} (hB : 2*B < n+1)
    {s t : Corner} (hst : s ≠ t) {S : Finset (Fin n)} (hS : S.Nonempty)
    (hs : ∀ v ∈ S, A ≤ cornerDistance s v ∧ cornerDistance s v ≤ B)
    (ht : ∀ v ∈ S, A ≤ cornerDistance t v ∧ cornerDistance t v ≤ B) : False := by
  obtain ⟨v, hv⟩ := hS
  have hsv := (hs v hv).2
  have htv := (ht v hv).2
  have hvn := v.isLt
  cases s <;> cases t
  · exact hst rfl
  · dsimp [cornerDistance] at hsv htv
    omega
  · dsimp [cornerDistance] at hsv htv
    omega
  · exact hst rfl

theorem core_category_cycle_sets_disjoint {n q A B : ℕ} (hn : 2 ≤ n)
    (hB : 2*B < n+1) (c : Fin q → CoreCycleCategory) (hc : CoreCategoriesDisjoint c)
    (R : Equiv.Perm (Fin n)) :
    Pairwise (fun i j => Disjoint
      (categoryCycleSet R (fun i => (c i).lengthIndex) (fun i => CategoryAdmissible A B (c i)) i)
      (categoryCycleSet R (fun i => (c i).lengthIndex) (fun i => CategoryAdmissible A B (c i)) j)) := by
  classical
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro orb hi hj
  obtain ⟨hiorb, his, hir⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjorb, hjs, hjr⟩ := Finset.mem_filter.mp hj
  have hlen : (c i).lengthIndex = (c j).lengthIndex := by
    have hli := Section5.cycleOrbit_length R (c i).lengthIndex orb hiorb
    have hlj := Section5.cycleOrbit_length R (c j).lengthIndex orb hjorb
    omega
  by_cases hs : (c i).side = (c j).side
  · exact hc n hn i j hij hs hlen (categorySetRootDepth (c i).side orb.toFinset)
      ⟨hir, by simpa only [hs] using hjr⟩
  · have hne : orb.toFinset.Nonempty := by
      apply Finset.card_pos.mp
      rw [Section5.cycleOrbit_card R (c i).lengthIndex orb hiorb]
      omega
    exact opposite_core_sets_disjoint hB hs hne his hjs

theorem core_category_expectation_eq_rank_sum {n q : ℕ} (hn : 2 ≤ n)
    (hB : 2*idealCoreUpper n < n+1) (w : Weights n)
    (c : Fin q → CoreCycleCategory) (hc : CoreCategoriesDisjoint c) (r : Fin q → ℕ) :
    (∫ e, ∏ i, ((coreCategoryCount (raceRankPermutation e) (c i)).descFactorial (r i) : ℝ)
      ∂exponentialRace w) =
      (∑ t : CategoryCycleVertex (fun i => (c i).lengthIndex) r ↪ Fin n,
        if ∀ b, CategoryAdmissible (idealCoreLower n) (idealCoreUpper n) (c b.1)
          (categoryBlockVertexSet t b) then
          (exponentialRace w).real {e | ∀ x, raceRank e (t x) =
            (t (categoryBlockPermutation (fun i => (c i).lengthIndex) r x)).val+1} else 0) /
        ∏ i, (((c i).lengthIndex+1 : ℕ) : ℝ)^r i := by
  classical
  exact category_factorial_expectation_eq_rank_sum w (fun i => (c i).lengthIndex) r
    (fun i => CategoryAdmissible (idealCoreLower n) (idealCoreUpper n) (c i))
    (core_category_cycle_sets_disjoint hn hB c hc)

end Luce.Section6
