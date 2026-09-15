import Luce.RaceOrder
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# Deterministic insertion and path estimates from Section 5

This file proves the deterministic part of `fixed_points.tex`, lines
1127–1136.  The permutation is the map from labels to ranks, and edges
point from the source label to a possible target rank.  The finite path
bound includes repeated sources; restriction to distinct sources is an
explicit finite-set inclusion.  No probabilistic insertion inequality is
claimed by this file.
-/

noncomputable section
open scoped BigOperators

namespace Luce

attribute [local instance] Classical.propDecidable

/-- The number of background clocks strictly below a proposed insertion time. -/
def clockBeforeCount {n : ℕ} (clocks : Fin n → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun i => clocks i < t).card

/-- Changing only the labels in `s` changes any threshold count by at most
`s.card`; this is the rank perturbation used in `eq:approximate-permutation-path`.
Neither distinctness nor positivity is needed for the threshold-count assertion. -/
theorem clockBeforeCount_le_add_of_eq_off {n : ℕ}
    (old new : Fin n → ℝ) (s : Finset (Fin n))
    (hsame : ∀ i, i ∉ s → new i = old i) (t : ℝ) :
    clockBeforeCount new t ≤ clockBeforeCount old t + s.card := by
  classical
  have hsub : (Finset.univ.filter fun i => new i < t) ⊆
      (Finset.univ.filter fun i => old i < t) ∪ s := by
    intro i hi
    by_cases his : i ∈ s
    · exact Finset.mem_union_right _ his
    · apply Finset.mem_union_left
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rwa [hsame i his] at hi
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- The symmetric threshold-count form of the manuscript's finite-swap
rank perturbation. -/
theorem clockBeforeCount_dist_le_of_eq_off {n : ℕ}
    (old new : Fin n → ℝ) (s : Finset (Fin n))
    (hsame : ∀ i, i ∉ s → new i = old i) (t : ℝ) :
    Nat.dist (clockBeforeCount new t) (clockBeforeCount old t) ≤ s.card := by
  have h₁ := clockBeforeCount_le_add_of_eq_off old new s hsame t
  have h₂ := clockBeforeCount_le_add_of_eq_off new old s
    (fun i hi => (hsame i hi).symm) t
  unfold Nat.dist
  omega

lemma clockBeforeCount_mono {n : ℕ} (clocks : Fin n → ℝ) :
    Monotone (clockBeforeCount clocks) := by
  intro s t hst
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans_le hst

lemma clockBeforeCount_le {n : ℕ} (clocks : Fin n → ℝ) (t : ℝ) :
    clockBeforeCount clocks t ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

lemma clockBeforeCount_arrivalTime {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (k : Fin n) :
    clockBeforeCount clocks (arrivalTime clocks hinj k) = k.val := by
  exact congrArg Fin.val ((rankPermutation clocks hinj).apply_symm_apply k)

lemma clockBeforeCount_lt_of_clock_lt {n : ℕ} (clocks : Fin n → ℝ)
    (i : Fin n) {t : ℝ} (ht : clocks i < t) :
    clockBeforeCount clocks (clocks i) < clockBeforeCount clocks t := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.trans ht
  · intro he
    have hi : i ∈ (Finset.univ.filter fun j => clocks j < t) := by simp [ht]
    rw [← he] at hi
    simp at hi

/-- Strict membership above an order statistic is exactly a lower bound on
the number of clocks before the proposed time. -/
theorem arrivalTime_lt_iff_clockBeforeCount {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (k : Fin n) (t : ℝ) :
    arrivalTime clocks hinj k < t ↔ k.val + 1 ≤ clockBeforeCount clocks t := by
  constructor
  · intro ht
    have hh := clockBeforeCount_lt_of_clock_lt clocks
      (drawPermutation clocks hinj k) ht
    change clockBeforeCount clocks (arrivalTime clocks hinj k) < _ at hh
    rw [clockBeforeCount_arrivalTime] at hh
    omega
  · intro ht
    by_contra hn
    have hh := clockBeforeCount_mono clocks (le_of_not_gt hn)
    rw [clockBeforeCount_arrivalTime] at hh
    omega

/-- Strict membership below an order statistic has the expected count
description whenever the proposed time is not a background clock. -/
theorem lt_arrivalTime_iff_clockBeforeCount {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (k : Fin n) (t : ℝ)
    (hne : t ≠ arrivalTime clocks hinj k) :
    t < arrivalTime clocks hinj k ↔ clockBeforeCount clocks t < k.val + 1 := by
  have h := arrivalTime_lt_iff_clockBeforeCount clocks hinj k t
  constructor
  · intro ht
    have hn : ¬arrivalTime clocks hinj k < t := not_lt_of_ge ht.le
    have := mt h.mpr hn
    omega
  · intro ht
    have hn : ¬arrivalTime clocks hinj k < t := fun hlt => by
      have := h.mp hlt
      omega
    exact lt_of_le_of_ne (le_of_not_gt hn) hne

/-- The manuscript's open window with sentinel endpoints `T₀ = 0` and
`Tₙ₊₁ = ∞`. The upper sentinel is represented by a vacuous upper condition. -/
def GhostWindowByOrder {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (ell : ℕ) (j : Fin n) (t : ℝ) : Prop :=
  (if hlower : ell < j.val + 1 then
    arrivalTime clocks hinj ⟨j.val - ell, by omega⟩ < t
  else 0 < t) ∧
  (if hupper : j.val + 1 + ell ≤ n then
    t < arrivalTime clocks hinj ⟨j.val + ell, by omega⟩
  else True)

/-- Membership in a genuine open window implies the count inequalities
even when the proposed time coincides with a different background clock. -/
theorem ghostWindowByOrder_count_bounds {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (hnonneg : ∀ i, 0 ≤ clocks i)
    (ell : ℕ) (j : Fin n) (t : ℝ)
    (hwindow : GhostWindowByOrder clocks hinj ell j t) :
    0 < t ∧ j.val + 1 ≤ clockBeforeCount clocks t + ell ∧
      clockBeforeCount clocks t < j.val + 1 + ell := by
  have hlow (k : Fin n) := arrivalTime_lt_iff_clockBeforeCount clocks hinj k t
  have hupp (k : Fin n) (hk : t < arrivalTime clocks hinj k) :
      clockBeforeCount clocks t < k.val + 1 := by
    have hh := clockBeforeCount_mono clocks hk.le
    rw [clockBeforeCount_arrivalTime] at hh
    omega
  have hcount := clockBeforeCount_le clocks t
  unfold GhostWindowByOrder at hwindow
  split_ifs at hwindow with hl hu hu
  · obtain ⟨h₁, h₂⟩ := hwindow
    have ht : 0 < t := (hnonneg _).trans_lt h₁
    have hlc := (hlow _).mp h₁
    have huc := hupp _ h₂
    dsimp only at hlc huc
    exact ⟨ht, by omega, by omega⟩
  · obtain ⟨h₁, _⟩ := hwindow
    have ht : 0 < t := (hnonneg _).trans_lt h₁
    have hlc := (hlow _).mp h₁
    dsimp only at hlc
    exact ⟨ht, by omega, by omega⟩
  · obtain ⟨ht, h₂⟩ := hwindow
    have huc := hupp _ h₂
    dsimp only at huc
    exact ⟨ht, by omega, by omega⟩
  · exact ⟨hwindow.1, by omega, by omega⟩

/-- Exact correspondence between `eq:ghost-window` and the rank-count
window used for insertion.  Ties with the proposed time are excluded here;
independent continuous clocks discharge that condition almost surely. -/
theorem ghostWindowByOrder_iff_count {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (hnonneg : ∀ i, 0 ≤ clocks i)
    (ell : ℕ) (j : Fin n) (t : ℝ) (havoid : ∀ i, t ≠ clocks i) :
    GhostWindowByOrder clocks hinj ell j t ↔
      0 < t ∧ j.val + 1 ≤ clockBeforeCount clocks t + ell ∧
        clockBeforeCount clocks t < j.val + 1 + ell := by
  have hlow (k : Fin n) := arrivalTime_lt_iff_clockBeforeCount clocks hinj k t
  have hupp (k : Fin n) := lt_arrivalTime_iff_clockBeforeCount clocks hinj k t
    (havoid (drawPermutation clocks hinj k))
  have hcount := clockBeforeCount_le clocks t
  unfold GhostWindowByOrder
  split_ifs with hl hu hu
  · rw [hlow, hupp]
    dsimp only
    constructor
    · rintro ⟨h₁, h₂⟩
      have ht : 0 < t := (hnonneg (drawPermutation clocks hinj
        ⟨j.val - ell, by omega⟩)).trans_lt ((hlow _).mpr h₁)
      exact ⟨ht, by omega, by omega⟩
    · rintro ⟨_, h₁, h₂⟩
      exact ⟨by omega, by omega⟩
  · rw [hlow]
    dsimp only
    simp only [and_true]
    constructor
    · intro h₁
      have ht : 0 < t := (hnonneg (drawPermutation clocks hinj
        ⟨j.val - ell, by omega⟩)).trans_lt ((hlow _).mpr h₁)
      exact ⟨ht, by omega, by omega⟩
    · rintro ⟨_, h₁, _⟩
      omega
  · rw [hupp]
    dsimp only
    constructor
    · rintro ⟨ht, h₂⟩
      exact ⟨ht, by omega, by omega⟩
    · rintro ⟨ht, _, h₂⟩
      exact ⟨ht, by omega⟩
  · simp only [and_true]
    constructor
    · intro ht
      exact ⟨ht, by omega, by omega⟩
    · exact fun h => h.1

/-- Count-window membership costs at most `ell` ranks in zero-based
coordinates; hence the source's more generous `ell + 1` also holds. -/
theorem clockBeforeCount_window_dist {n : ℕ} (clocks : Fin n → ℝ)
    (ell : ℕ) (j : Fin n) (t : ℝ)
    (hlower : j.val + 1 ≤ clockBeforeCount clocks t + ell)
    (hupper : clockBeforeCount clocks t < j.val + 1 + ell) :
    Nat.dist (clockBeforeCount clocks t) j.val ≤ ell := by
  unfold Nat.dist
  omega

/-- The complete deterministic implication used after swapping replacement
clocks: old-window success gives approximate ranks in the new background. -/
theorem rankPermutation_dist_le_of_count_window {n : ℕ}
    (old new : Fin n → ℝ) (s : Finset (Fin n))
    (hsame : ∀ i, i ∉ s → new i = old i)
    (hinj : Function.Injective new) (ell : ℕ) (i j : Fin n)
    (hlower : j.val + 1 ≤ clockBeforeCount old (new i) + ell)
    (hupper : clockBeforeCount old (new i) < j.val + 1 + ell) :
    Nat.dist ((rankPermutation new hinj i).val) j.val ≤ ell + s.card := by
  change Nat.dist (clockBeforeCount new (new i)) j.val ≤ ell + s.card
  calc
    _ ≤ Nat.dist (clockBeforeCount new (new i)) (clockBeforeCount old (new i)) +
        Nat.dist (clockBeforeCount old (new i)) j.val := Nat.dist.triangle_inequality _ _ _
    _ ≤ s.card + ell := Nat.add_le_add
      (clockBeforeCount_dist_le_of_eq_off old new s hsame (new i))
      (clockBeforeCount_window_dist old ell j (new i) hlower hupper)
    _ = ell + s.card := Nat.add_comm _ _

/-- Edges of the deterministic approximate rank graph, with labels and
positions both represented by `Fin n`. -/
def ApproximatePermutationEdge {n : ℕ} (σ : Equiv.Perm (Fin n)) (q : ℕ)
    (u v : Fin n) : Prop := Nat.dist (σ u).val v.val ≤ q

/-- The zero-based natural-distance convention is exactly the paper's
absolute difference of one-based ranks and labels. -/
theorem approximatePermutationEdge_iff_oneBased {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (q : ℕ) (u v : Fin n) :
    ApproximatePermutationEdge σ q u v ↔
      |((σ u).val : ℤ) + 1 - ((v.val : ℤ) + 1)| ≤ (q : ℤ) := by
  simp only [ApproximatePermutationEdge, Nat.dist, abs_le]
  omega

/-- A length-`m` path ending at `v`.  The tuple consists of precisely the
`m` source vertices; the endpoint is appended separately. -/
def ApproximatePermutationPath {n m : ℕ} (σ : Equiv.Perm (Fin n)) (q : ℕ)
    (v : Fin n) (u : Fin m → Fin n) : Prop :=
  ∀ a, ApproximatePermutationEdge σ q (u a)
    ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)

/-- Each approximate edge is encoded by one of `2*q+1` integer offsets. -/
def approximatePermutationPathCode {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (q : ℕ) (v : Fin n)
    (u : {u : Fin m → Fin n // ApproximatePermutationPath σ q v u}) :
    Fin m → Fin (2 * q + 1) := fun a =>
  ⟨(σ (u.val a)).val + q -
    ((Fin.snoc u.val v : Fin (m + 1) → Fin n) a.succ).val, by
    have h := u.property a
    dsimp [ApproximatePermutationEdge] at h
    unfold Nat.dist at h
    omega⟩

/-- For fixed endpoint, the sequence of offsets determines the path by
backward induction.  This checks the unique-preimage counting step in the
last paragraph of the proof of `lem:finite-insertion-path`. -/
theorem approximatePermutationPathCode_injective {n m : ℕ}
    (σ : Equiv.Perm (Fin n)) (q : ℕ) (v : Fin n) :
    Function.Injective (approximatePermutationPathCode (m := m) σ q v) := by
  intro u w he
  have hfull : (Fin.snoc u.val v : Fin (m + 1) → Fin n) = Fin.snoc w.val v := by
    funext a
    induction a using Fin.reverseInduction with
    | last => simp
    | cast a ih =>
      simp only [Fin.snoc_castSucc]
      apply σ.injective
      apply Fin.ext
      have hc := congrArg (fun f : Fin m → Fin (2 * q + 1) => (f a).val) he
      dsimp [approximatePermutationPathCode] at hc
      have hu := u.property a
      have hw := w.property a
      dsimp [ApproximatePermutationEdge] at hu hw
      rw [ih] at hc hu
      unfold Nat.dist at hu hw
      omega
  apply Subtype.ext
  funext a
  have ha := congrFun hfull a.castSucc
  simpa only [Fin.snoc_castSucc] using ha

/-- At most `(2*q+1)^m` directed approximate-permutation paths end at any
fixed vertex.  This is `fixed_points.tex`, lines 1131–1136.  Length zero
is included and has exactly one empty source tuple. -/
theorem approximatePermutationPath_count_le {n m : ℕ}
    (σ : Equiv.Perm (Fin n)) (q : ℕ) (v : Fin n) :
    (Finset.univ.filter (ApproximatePermutationPath (m := m) σ q v)).card ≤
      (2 * q + 1) ^ m := by
  classical
  have hc := Fintype.card_le_of_injective
    (approximatePermutationPathCode (m := m) σ q v)
    (approximatePermutationPathCode_injective σ q v)
  simpa only [Fintype.card_subtype, Fintype.card_pi_const, Fintype.card_fin] using hc

/-- The genuine-cycle distinct-source condition only restricts the counted
paths, so dropping it is a proved overcounting step. -/
theorem distinct_approximatePermutationPath_count_le {n m : ℕ}
    (σ : Equiv.Perm (Fin n)) (q : ℕ) (v : Fin n) :
    (Finset.univ.filter fun u : Fin m → Fin n =>
      Function.Injective u ∧ ApproximatePermutationPath σ q v u).card ≤
      (2 * q + 1) ^ m := by
  classical
  apply le_trans (Finset.card_le_card ?_) (approximatePermutationPath_count_le σ q v)
  intro u hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.2⟩

/-- A fixed time is contained in at most `2*ell+1` count windows.  This is
the deterministic multiplicity assertion preceding `eq:ghost-row-bound`;
it holds for any count and includes the clipped endpoint windows. -/
theorem countWindow_multiplicity_le (n ell c : ℕ) :
    (Finset.univ.filter fun j : Fin n =>
      j.val + 1 ≤ c + ell ∧ c < j.val + 1 + ell).card ≤ 2 * ell + 1 := by
  let f : {j : Fin n // j.val + 1 ≤ c + ell ∧ c < j.val + 1 + ell} →
      Fin (2 * ell + 1) := fun j => ⟨j.val.val + ell - c, by
        have hj := j.property
        omega⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg Fin.val he
    dsimp [f] at hv
    have hi := i.property
    have hj := j.property
    omega
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_subtype, Fintype.card_fin] using hc

/-- The same multiplicity bound for the manuscript's exact open windows,
using the proved order-statistic/count correspondence. -/
theorem ghostWindowByOrder_multiplicity_le {n : ℕ} (clocks : Fin n → ℝ)
    (hinj : Function.Injective clocks) (hnonneg : ∀ i, 0 ≤ clocks i)
    (ell : ℕ) (t : ℝ) :
    (Finset.univ.filter fun j : Fin n =>
      GhostWindowByOrder clocks hinj ell j t).card ≤ 2 * ell + 1 := by
  apply le_trans (Finset.card_le_card ?_) (countWindow_multiplicity_le n ell
    (clockBeforeCount clocks t))
  intro j hj
  have hj' := ghostWindowByOrder_count_bounds clocks hinj hnonneg ell j t
    (Finset.mem_filter.mp hj).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'.2⟩

end Luce
