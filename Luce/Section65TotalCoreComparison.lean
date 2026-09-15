import Luce.Section65ActiveCorners
import Luce.Section65FiniteCountCover
import Luce.Section6CoreCategoryDisjoint
import Luce.Section6Lemma67Definitions

noncomputable section
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

def lowRootLabels65 (side : Corner) (n : ℕ) (δ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => cornerDistance side v < idealCoreLower n ∧
    (cornerDistance side v : ℝ)/(n : ℝ) ≤ δ)

def highRootLabels65 (side : Corner) (n : ℕ) (δ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => idealCoreUpper n < cornerDistance side v ∧
    (cornerDistance side v : ℝ)/(n : ℝ) ≤ δ)

def allCoreCycle65 {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (side : Corner) (c : ↥(Section5.cycleOrbits R k)) : Prop :=
  ∀ v ∈ c.val.toFinset, idealCoreLower n ≤ cornerDistance side v ∧ cornerDistance side v ≤ idealCoreUpper n

theorem cornerCoreCount_filtered65 {n : ℕ} (R : Equiv.Perm (Fin n)) (side : Corner) (k : ℕ) :
    coreCategoryCount R (cornerCoreCategory65 side k) =
      (Finset.univ.filter (allCoreCycle65 R k side)).card := by
  classical
  letI : DecidablePred (allCoreCycle65 R k side) := fun c => Classical.propDecidable _
  have hmem (c : ↥(Section5.cycleOrbits R k)) :
      c ∈ Finset.univ.filter (allCoreCycle65 R k side) ↔ allCoreCycle65 R k side c := by
    exact (Finset.mem_filter).trans (and_iff_right (Finset.mem_univ c))
  rw [coreCategoryCount_eq_filtered65]
  apply congrArg (Finset.card : Finset ↥(Section5.cycleOrbits R k) → ℕ)
  ext c
  constructor
  · intro hc
    exact (hmem c).mpr (Finset.mem_filter.mp hc).2.1
  · intro hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hmem c).mp hc,trivial⟩

theorem totalCoreCount_le65 {n : ℕ} (R : Equiv.Perm (Fin n)) (left right : EndpointBehavior) (k : ℕ)
    (hsep : 2*idealCoreUpper n < n+1) : totalCoreCount65 R left right k ≤ (Section5.cycleCount R k : ℝ) := by
  classical
  unfold totalCoreCount65
  simp_rw [cornerCoreCount_filtered65]
  have hh := disjoint_filter_card_sum_le65
    (fun s : ActiveCorner65 left right => allCoreCycle65 R k s.val) (by
      intro c s t hs ht
      apply Subtype.ext
      by_contra hne
      exact opposite_core_sets_disjoint hsep hne ⟨_,Section5.cycleMaximum_mem R k c⟩ hs ht)
  simpa only [Fintype.card_coe,Section5.cycleCount] using hh

theorem not_offActiveLabels65 {n : ℕ} (left right : EndpointBehavior) (δ : ℝ) (v : Fin n)
    (hv : v ∉ offActiveLabels left right n δ) :
    ∃ s : ActiveCorner65 left right, (cornerDistance s.val v : ℝ)/(n : ℝ) ≤ δ := by
  classical
  have hnot : ¬ ((left.active → δ ≤ (cornerDistance .left v : ℝ)/(n : ℝ)) ∧
      (right.active → δ ≤ (cornerDistance .right v : ℝ)/(n : ℝ))) := by
    simpa [offActiveLabels,cornerDistance,Nat.cast_add,Nat.cast_one] using hv
  by_cases hL : left.active ∧ (cornerDistance .left v : ℝ)/(n : ℝ) < δ
  · exact ⟨⟨.left,hL.1⟩,hL.2.le⟩
  · have hl : left.active → δ ≤ (cornerDistance .left v : ℝ)/(n : ℝ) := by
      intro ha
      exact le_of_not_gt (fun hh => hL ⟨ha,hh⟩)
    have hr : ¬ (right.active → δ ≤ (cornerDistance .right v : ℝ)/(n : ℝ)) := fun hr => hnot ⟨hl,hr⟩
    push_neg at hr
    exact ⟨⟨.right,hr.1⟩,hr.2.le⟩

theorem totalCoreCount_error65 {n : ℕ} (R : Equiv.Perm (Fin n)) (left right : EndpointBehavior)
    (k : ℕ) (δ : ℝ) (hsep : 2*idealCoreUpper n < n+1) :
    |(Section5.cycleCount R k : ℝ)-totalCoreCount65 R left right k| ≤
      (selectedRootCycleCount R k (offActiveLabels left right n δ) : ℝ)+
      ∑ s : ActiveCorner65 left right,
        ((selectedRootCycleCount R k (lowRootLabels65 s.val n δ) : ℝ)+
         (selectedRootCycleCount R k (highRootLabels65 s.val n δ) : ℝ)+
         (intervalDiscardedCycleCount R s.val k (idealCoreLower n) (idealCoreUpper n) : ℝ)) := by
  classical
  let p (c : ↥(Section5.cycleOrbits R k)) := Section5.cycleMaximum R k c ∈ offActiveLabels left right n δ
  let low (s : ActiveCorner65 left right) (c : ↥(Section5.cycleOrbits R k)) :=
    Section5.cycleMaximum R k c ∈ lowRootLabels65 s.val n δ
  let high (s : ActiveCorner65 left right) (c : ↥(Section5.cycleOrbits R k)) :=
    Section5.cycleMaximum R k c ∈ highRootLabels65 s.val n δ
  let disc (s : ActiveCorner65 left right) (c : ↥(Section5.cycleOrbits R k)) :=
    (idealCoreLower n : ℝ) ≤ (cornerDistance s.val (Section5.cycleMaximum R k c) : ℝ) ∧
    (cornerDistance s.val (Section5.cycleMaximum R k c) : ℝ) ≤ (idealCoreUpper n : ℝ) ∧
    ∃ v ∈ c.val.toFinset, ¬ ((idealCoreLower n : ℝ) ≤ (cornerDistance s.val v : ℝ) ∧
      (cornerDistance s.val v : ℝ) ≤ (idealCoreUpper n : ℝ))
  let q (s : ActiveCorner65 left right) (c : ↥(Section5.cycleOrbits R k)) :=
    allCoreCycle65 R k s.val c ∨ low s c ∨ high s c ∨ disc s c
  have hc : ∀ c, p c ∨ ∃ s, q s c := by
    intro c
    by_cases hp : p c
    · exact Or.inl hp
    right
    obtain ⟨s,hs⟩ := not_offActiveLabels65 left right δ (Section5.cycleMaximum R k c) hp
    refine ⟨s,?_⟩
    by_cases hl : cornerDistance s.val (Section5.cycleMaximum R k c) < idealCoreLower n
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl,hs⟩))
    by_cases hh : idealCoreUpper n < cornerDistance s.val (Section5.cycleMaximum R k c)
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh,hs⟩)))
    by_cases hcore : allCoreCycle65 R k s.val c
    · exact Or.inl hcore
    · refine Or.inr (Or.inr (Or.inr ⟨by exact_mod_cast (le_of_not_gt hl),
        by exact_mod_cast (le_of_not_gt hh),?_⟩))
      change ¬ (∀ v ∈ c.val.toFinset, idealCoreLower n ≤ cornerDistance s.val v ∧
        cornerDistance s.val v ≤ idealCoreUpper n) at hcore
      push_neg at hcore
      obtain ⟨v,hv,hbad⟩ := hcore
      refine ⟨v,hv,?_⟩
      intro hok
      have hok' : idealCoreLower n ≤ cornerDistance s.val v ∧ cornerDistance s.val v ≤ idealCoreUpper n := by
        exact_mod_cast hok
      exact (not_le.mpr (hbad hok'.1)) hok'.2
  have hcover : (Fintype.card ↥(Section5.cycleOrbits R k) : ℝ) ≤
      ((Finset.univ.filter p).card : ℝ)+
        ∑ s : ActiveCorner65 left right, ((Finset.univ.filter (q s)).card : ℝ) := by
    convert covered_filter_card65 p q hc using 1 <;> congr
    funext s
    congr
  have hq (s : ActiveCorner65 left right) : ((Finset.univ.filter (q s)).card : ℝ) ≤
      (coreCategoryCount R (cornerCoreCategory65 s.val k) : ℝ)+
      ((selectedRootCycleCount R k (lowRootLabels65 s.val n δ) : ℝ)+
       (selectedRootCycleCount R k (highRootLabels65 s.val n δ) : ℝ)+
       (intervalDiscardedCycleCount R s.val k (idealCoreLower n) (idealCoreUpper n) : ℝ)) := by
    rw [cornerCoreCount_filtered65]
    have h1 := filter_card_le_add65 (q s) (allCoreCycle65 R k s.val) (fun c => low s c ∨ high s c ∨ disc s c)
      (fun c h => h)
    have h2 := filter_card_le_add65 (fun c => low s c ∨ high s c ∨ disc s c) (low s) (fun c => high s c ∨ disc s c)
      (fun c h => h)
    have h3 := filter_card_le_add65 (fun c => high s c ∨ disc s c) (high s) (disc s) (fun c h => h)
    have hnat := h1.trans (Nat.add_le_add_left (h2.trans (Nat.add_le_add_left h3 _)) _)
    have hreal : ((Finset.univ.filter (q s)).card : ℝ) ≤
      ((Finset.univ.filter (allCoreCycle65 R k s.val)).card : ℝ)+
      (((Finset.univ.filter (low s)).card : ℝ)+(((Finset.univ.filter (high s)).card : ℝ)+
        ((Finset.univ.filter (disc s)).card : ℝ))) := by exact_mod_cast hnat
    simpa only [selectedRootCycleCount,intervalDiscardedCycleCount,low,high,disc,add_assoc] using hreal
  have hsum : (∑ s : ActiveCorner65 left right, ((Finset.univ.filter (q s)).card : ℝ)) ≤
      ∑ s : ActiveCorner65 left right,
        ((coreCategoryCount R (cornerCoreCategory65 s.val k) : ℝ)+
        ((selectedRootCycleCount R k (lowRootLabels65 s.val n δ) : ℝ)+
         (selectedRootCycleCount R k (highRootLabels65 s.val n δ) : ℝ)+
         (intervalDiscardedCycleCount R s.val k (idealCoreLower n) (idealCoreUpper n) : ℝ))) := by
    apply Finset.sum_le_sum
    intro s hs
    convert hq s using 1 <;> congr
  have hb := hcover.trans (add_le_add le_rfl hsum)
  rw [Finset.sum_add_distrib] at hb
  have hpEq : ((Finset.univ.filter p).card : ℝ) = (selectedRootCycleCount R k (offActiveLabels left right n δ) : ℝ) := by
    rfl
  rw [hpEq] at hb
  change (Fintype.card ↥(Section5.cycleOrbits R k) : ℝ) ≤ _ at hb
  simp only [Fintype.card_coe] at hb
  change (Section5.cycleCount R k : ℝ) ≤ _ at hb
  rw [abs_of_nonneg (sub_nonneg.mpr (totalCoreCount_le65 R left right k hsep))]
  dsimp [totalCoreCount65]
  linarith

end Luce.Section6
