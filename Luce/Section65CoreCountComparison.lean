import Luce.Section6CoreCategoryDefinitions
import Luce.Section6DiscardedCountDefinitions
import Luce.Section5MaximumRoot

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem categorySetRootDepth_cycle65 {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (c : ↥(Section5.cycleOrbits R k)) (side : Corner) :
    categorySetRootDepth side c.val.toFinset = cornerDistance side (Section5.cycleMaximum R k c) := by
  have he : c.val.toFinset.sup (fun v => v.val) = (Section5.cycleMaximum R k c).val := by
    apply le_antisymm
    · exact Finset.sup_le (fun v hv => Section5.cycleMaximum_upper R k c v hv)
    · exact Finset.le_sup (f := fun v : Fin n => v.val) (Section5.cycleMaximum_mem R k c)
  cases side <;> simp only [categorySetRootDepth,cornerDistance,he]

theorem coreCategoryCount_eq_filtered65 {n : ℕ} (R : Equiv.Perm (Fin n))
    (c : CoreCycleCategory) :
    coreCategoryCount R c = (Finset.univ.filter (fun d : ↥(Section5.cycleOrbits R c.lengthIndex) =>
      (∀ v ∈ d.val.toFinset, idealCoreLower n ≤ cornerDistance c.side v ∧
        cornerDistance c.side v ≤ idealCoreUpper n) ∧
      c.rootWindow.Allows n (cornerDistance c.side (Section5.cycleMaximum R c.lengthIndex d)))).card := by
  classical
  unfold coreCategoryCount
  have he := Finset.card_bij
    (fun d hd => (⟨d,(Finset.mem_filter.mp hd).1⟩ : ↥(Section5.cycleOrbits R c.lengthIndex)))
    (t := Finset.univ.filter (fun d : ↥(Section5.cycleOrbits R c.lengthIndex) =>
      CategoryAdmissible (idealCoreLower n) (idealCoreUpper n) c d.val.toFinset))
    (by intro d hd; simpa using (Finset.mem_filter.mp hd).2)
    (by intro d hd e he h; exact congrArg Subtype.val h)
    (by intro d hd; exact ⟨d.val,Finset.mem_filter.mpr ⟨d.property,(Finset.mem_filter.mp hd).2⟩,rfl⟩)
  refine he.trans ?_
  congr 1
  ext d
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,CategoryAdmissible,categorySetRootDepth_cycle65]

theorem filter_card_le_add65 {ι : Type*} [Fintype ι] (p q r : ι → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (h : ∀ i, p i → q i ∨ r i) :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card+(Finset.univ.filter r).card := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := h i
  by_cases hp : p i <;> by_cases hq : q i <;> by_cases hr : r i <;> simp_all

theorem coreCount_le_windowCount65 {n : ℕ} (R : Equiv.Perm (Fin n))
    (c : CoreCycleCategory) :
    coreCategoryCount R c ≤ (Finset.univ.filter (fun d : ↥(Section5.cycleOrbits R c.lengthIndex) =>
      c.rootWindow.Allows n (cornerDistance c.side (Section5.cycleMaximum R c.lengthIndex d)))).card := by
  classical
  rw [coreCategoryCount_eq_filtered65]
  apply Finset.card_le_card
  intro d hd
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2.2⟩

theorem windowCount_sub_coreCount_le_discarded65 {n : ℕ} (R : Equiv.Perm (Fin n))
    (c : CoreCycleCategory)
    (hw : ∀ v : Fin n, c.rootWindow.Allows n (cornerDistance c.side v) →
      idealCoreLower n ≤ cornerDistance c.side v ∧ cornerDistance c.side v ≤ idealCoreUpper n) :
    ((Finset.univ.filter (fun d : ↥(Section5.cycleOrbits R c.lengthIndex) =>
      c.rootWindow.Allows n (cornerDistance c.side (Section5.cycleMaximum R c.lengthIndex d)))).card : ℝ) -
      (coreCategoryCount R c : ℝ) ≤
        (intervalDiscardedCycleCount R c.side c.lengthIndex (idealCoreLower n) (idealCoreUpper n) : ℝ) := by
  classical
  rw [sub_le_iff_le_add,coreCategoryCount_eq_filtered65]
  unfold intervalDiscardedCycleCount
  norm_cast
  rw [add_comm]
  apply filter_card_le_add65
  intro d hd
  by_cases hcore : ∀ v ∈ d.val.toFinset, idealCoreLower n ≤ cornerDistance c.side v ∧
      cornerDistance c.side v ≤ idealCoreUpper n
  · exact Or.inl ⟨hcore,hd⟩
  · right
    have hr := hw (Section5.cycleMaximum R c.lengthIndex d) hd
    refine ⟨by exact_mod_cast hr.1,by exact_mod_cast hr.2,?_⟩
    push_neg at hcore
    obtain ⟨v,hv,hvbad⟩ := hcore
    refine ⟨v,hv,?_⟩
    intro hvok
    have hvok' : idealCoreLower n ≤ cornerDistance c.side v ∧ cornerDistance c.side v ≤ idealCoreUpper n := by
      exact_mod_cast hvok
    exact (not_le.mpr (hvbad hvok'.1)) hvok'.2

end Luce.Section6
