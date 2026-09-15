import Luce.Section5CycleProbability

/-!
# Single-coordinate replacement and cycle counting

Deterministic part of the alternative proof of Lemma 6.6 in
`fixed_points_sampled_profile.tex`. A path is encoded by offsets in {-1,0,1}.
The background and insertion time are common to all candidate roots.
-/

noncomputable section
open Function
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- A forward path whose first label is close to a given count, and whose
later labels are close to the background ranks of their predecessors. -/
def ReplacementPath {n k : ℕ} (f : Fin n → ℕ) (c : ℕ)
    (v : Fin (k+1) → Fin n) : Prop :=
  Nat.dist c (v 0).val ≤ 1 ∧
    ∀ a : Fin k, Nat.dist (f (v a.castSucc)) (v a.succ).val ≤ 1

def replacementPathCenter {n k : ℕ} (f : Fin n → ℕ) (c : ℕ)
    (v : Fin (k+1) → Fin n) : Fin (k+1) → ℕ :=
  Fin.cons c (fun a => f (v a.castSucc))

lemma replacementPath_dist {n k : ℕ} {f : Fin n → ℕ} {c : ℕ}
    {v : Fin (k+1) → Fin n} (hv : ReplacementPath f c v) (a : Fin (k+1)) :
    Nat.dist (replacementPathCenter f c v a) (v a).val ≤ 1 := by
  refine Fin.cases hv.1 (fun b => hv.2 b) a

def replacementPathCode {n k : ℕ} (f : Fin n → ℕ) (c : ℕ)
    (v : {v : Fin (k+1) → Fin n // ReplacementPath f c v}) :
    Fin (k+1) → Fin 3 := fun a =>
  ⟨replacementPathCenter f c v.val a + 1 - (v.val a).val, by
    have h := replacementPath_dist v.property a
    unfold Nat.dist at h
    omega⟩

theorem replacementPathCode_injective {n k : ℕ} (f : Fin n → ℕ) (c : ℕ) :
    Injective (replacementPathCode (k := k) f c) := by
  intro v w he
  apply Subtype.ext
  funext a
  induction a using Fin.induction with
  | zero =>
    apply Fin.ext
    have hc := congrArg (fun code => (code 0).val) he
    have hv := v.property.1
    have hw := w.property.1
    simp only [replacementPathCode, replacementPathCenter, Fin.cons_zero] at hc
    unfold Nat.dist at hv hw
    omega
  | succ a ih =>
    apply Fin.ext
    have hc := congrArg (fun code => (code a.succ).val) he
    have hv := v.property.2 a
    have hw := w.property.2 a
    simp only [replacementPathCode, replacementPathCenter, Fin.cons_succ] at hc
    rw [ih] at hc hv
    unfold Nat.dist at hv hw
    omega

theorem replacementPath_count_le {n k : ℕ} (f : Fin n → ℕ) (c : ℕ) :
    Fintype.card {v : Fin (k+1) → Fin n // ReplacementPath f c v} ≤ 3^(k+1) := by
  simpa only [Fintype.card_pi_const, Fintype.card_fin] using
    Fintype.card_le_of_injective _ (replacementPathCode_injective (k := k) f c)

lemma injective_update_clock {n : ℕ} {x : Fin n → ℝ} (hx : Injective x)
    {t : ℝ} (ht : ∀ j, t ≠ x j) (i : Fin n) : Injective (update x i t) := by
  intro a b hab
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · exact hb.symm
    · simp only [update_self, update_of_ne hb] at hab
      exact (ht b hab).elim
  · by_cases hb : b = i
    · subst b
      simp only [update_self, update_of_ne ha] at hab
      exact (ht a hab.symm).elim
    · simp only [update_of_ne ha, update_of_ne hb] at hab
      exact hx hab

/-- A successful root supplies a forward path in the common background.
Exact period ensures none of the intermediate sources is the replaced label. -/
theorem replacement_cycle_has_path {n k : ℕ} (x : Fin n → ℝ) (hx : Injective x)
    (t : ℝ) (ht : ∀ j, t ≠ x j) (i : Fin n)
    (hp : minimalPeriod (raceRankPermutation (update x i t) : Fin n → Fin n) i = k+1) :
    ∃ v : Fin (k+1) → Fin n,
      ReplacementPath (fun j => clockBeforeCount x (x j)) (clockBeforeCount x t) v ∧
      v (Fin.last k) = i := by
  let y := update x i t
  have hy : Injective y := injective_update_clock hx ht i
  obtain ⟨u, _, hui, hu⟩ := exists_cycle_tail_of_minimalPeriod (raceRankPermutation y) i hp
  refine ⟨Fin.snoc u i, ⟨?_, ?_⟩, Fin.snoc_last _ _⟩
  · have hr := congrArg Fin.val (hu 0)
    rw [raceRankPermutation_eq y hy] at hr
    change clockBeforeCount y (y ((Fin.cons i u : Fin (k+1) → Fin n) 0)) =
      ((Fin.snoc u i : Fin (k+1) → Fin n) 0).val at hr
    simp only [Fin.cons_zero] at hr
    have hsame : ∀ j ∉ ({i} : Finset (Fin n)), y j = x j := by
      intro j hj
      exact update_of_ne (by simpa using hj) _ _
    have hd := clockBeforeCount_dist_le_of_eq_off x y {i} hsame t
    have hyt : y i = t := update_self i t x
    rw [hyt] at hr
    rw [hr, Nat.dist_comm] at hd
    simpa using hd
  · intro a
    have hr := congrArg Fin.val (hu a.succ)
    rw [raceRankPermutation_eq y hy] at hr
    change clockBeforeCount y (y ((Fin.cons i u : Fin (k+1) → Fin n) a.succ)) =
      ((Fin.snoc u i : Fin (k+1) → Fin n) a.succ).val at hr
    simp only [Fin.cons_succ] at hr
    have hyu : y (u a) = x (u a) := update_of_ne (hui a) _ _
    rw [hyu] at hr
    have hsame : ∀ j ∉ ({i} : Finset (Fin n)), y j = x j := by
      intro j hj
      exact update_of_ne (by simpa using hj) _ _
    have hd := clockBeforeCount_dist_le_of_eq_off x y {i} hsame (x (u a))
    rw [hr, Nat.dist_comm] at hd
    simpa only [Fin.snoc_castSucc, Finset.card_singleton] using hd

/-- At most `3^(k+1)` roots acquire a cycle of exact length `k+1` when their
own coordinate is replaced by the same time. No stochastic hypotheses occur. -/
theorem single_replacement_cycle_count_le {n k : ℕ} (x : Fin n → ℝ)
    (hx : Injective x) (t : ℝ) (ht : ∀ j, t ≠ x j) :
    (Finset.univ.filter fun i =>
      minimalPeriod (raceRankPermutation (update x i t) : Fin n → Fin n) i = k+1).card
      ≤ 3^(k+1) := by
  let A := {i : Fin n //
    minimalPeriod (raceRankPermutation (update x i t) : Fin n → Fin n) i = k+1}
  let path (i : A) := (replacement_cycle_has_path x hx t ht i.val i.property).choose
  have hpath (i : A) := (replacement_cycle_has_path x hx t ht i.val i.property).choose_spec
  let code : A → {v : Fin (k+1) → Fin n //
      ReplacementPath (fun j => clockBeforeCount x (x j)) (clockBeforeCount x t) v} :=
    fun i => ⟨path i, (hpath i).1⟩
  have hcode : Injective code := by
    intro i j he
    apply Subtype.ext
    have hh := congrArg (fun v => v.val (Fin.last k)) he
    exact ((hpath i).2).symm.trans (hh.trans (hpath j).2)
  have hc := (Fintype.card_le_of_injective code hcode).trans
    (replacementPath_count_le (k := k) (fun j => clockBeforeCount x (x j)) (clockBeforeCount x t))
  simpa only [A, Fintype.card_subtype] using hc

end Luce.Section6
