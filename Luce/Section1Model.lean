import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Finite Luce models and deterministic exponential races

Labels and positions are indexed by `Fin n`, so the paper's label `k` is
represented by `k - 1`. `raceRank` retains the paper's one-based convention.
All results in this file are deterministic; probability measures for the
exponential clocks are constructed in `Luce.Section4ExponentialRace`.
-/

open scoped BigOperators

namespace Luce

/-- A finite family of strictly positive Luce weights. -/
structure Weights (n : ℕ) where
  rate : Fin n → ℝ
  positive : ∀ i, 0 < rate i

namespace Weights

variable {n : ℕ} (w : Weights n)

/-- Multiplying every rate by the same positive constant. -/
def scale (c : ℝ) (hc : 0 < c) : Weights n where
  rate i := c * w.rate i
  positive i := mul_pos hc (w.positive i)

/-- Total weight of a set of remaining labels. -/
noncomputable def total (s : Finset (Fin n)) : ℝ := ∑ i ∈ s, w.rate i

lemma total_nonneg (s : Finset (Fin n)) : 0 ≤ w.total s :=
  Finset.sum_nonneg fun i _ => (w.positive i).le

lemma total_pos {s : Finset (Fin n)} (hs : s.Nonempty) : 0 < w.total s :=
  Finset.sum_pos (fun i _ => w.positive i) hs

lemma rate_le_total {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) :
    w.rate i ≤ w.total s :=
  Finset.single_le_sum (fun j _ => (w.positive j).le) hi

/-- Proportional choice from a finite set; a removed label has chance zero. -/
noncomputable def choice (s : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ s then w.rate i / w.total s else 0

lemma choice_nonneg (s : Finset (Fin n)) (i : Fin n) : 0 ≤ w.choice s i := by
  unfold choice
  split_ifs
  · exact div_nonneg (w.positive i).le (w.total_nonneg s)
  · exact le_rfl

lemma choice_le_one (s : Finset (Fin n)) (i : Fin n) : w.choice s i ≤ 1 := by
  unfold choice
  split_ifs with hi
  · exact (div_le_one (w.total_pos ⟨i, hi⟩)).mpr (w.rate_le_total hi)
  · exact zero_le_one

lemma sum_choice {s : Finset (Fin n)} (hs : s.Nonempty) :
    ∑ i, w.choice s i = 1 := by
  classical
  simp only [choice]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (w.total_pos hs).ne'

lemma total_scale (c : ℝ) (hc : 0 < c) (s : Finset (Fin n)) :
    (w.scale c hc).total s = c * w.total s := by
  simp [total, scale, Finset.mul_sum]

lemma choice_scale (c : ℝ) (hc : 0 < c) (s : Finset (Fin n)) (i : Fin n) :
    (w.scale c hc).choice s i = w.choice s i := by
  unfold choice
  rw [total_scale]
  simp only [scale]
  split_ifs
  · exact mul_div_mul_left _ _ hc.ne'
  · rfl

/-- Equation `eq:luce-law`, with zero-based labels and positions. -/
noncomputable def mass (π : Equiv.Perm (Fin n)) : ℝ :=
  ∏ r, w.rate (π r) / ∑ j ∈ Finset.univ.filter (r ≤ ·), w.rate (π j)

lemma mass_pos (π : Equiv.Perm (Fin n)) : 0 < w.mass π := by
  classical
  apply Finset.prod_pos
  intro r _
  apply div_pos (w.positive _)
  apply Finset.sum_pos (fun j _ => w.positive _)
  exact ⟨r, by simp⟩

lemma mass_scale (c : ℝ) (hc : 0 < c) (π : Equiv.Perm (Fin n)) :
    (w.scale c hc).mass π = w.mass π := by
  classical
  apply Finset.prod_congr rfl
  intro r _
  simp only [scale, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc.ne'

end Weights

/-- Labels that have not been drawn immediately before position `k`. -/
def remaining {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => k ≤ π.symm i

/-- The draw order and its inverse have exactly the same fixed labels. -/
lemma inverse_fixed_iff {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    π.symm i = i ↔ π i = i := by
  constructor
  · intro h
    calc π i = π (π.symm i) := congrArg π h.symm
         _ = i := π.apply_symm_apply i
  · intro h
    calc π.symm i = π.symm (π i) := congrArg π.symm h.symm
         _ = i := π.symm_apply_apply i

/-- Equation `eq:fixed-process`: total number of fixed labels. -/
def fixedCount {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i => π i = i).card

lemma fixedCount_inverse {n : ℕ} (π : Equiv.Perm (Fin n)) :
    fixedCount π.symm = fixedCount π := by
  simp only [fixedCount, inverse_fixed_iff]

lemma remaining_nonempty {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (remaining π k).Nonempty := ⟨π k, by simp [remaining]⟩

/-- The explicit predictable probability in `eq:predictable-p`. -/
noncomputable def predictableChance {n : ℕ} (w : Weights n)
    (π : Equiv.Perm (Fin n)) (k : Fin n) : ℝ :=
  w.choice (remaining π k) k

lemma predictableChance_formula {n : ℕ} (w : Weights n)
    (π : Equiv.Perm (Fin n)) (k : Fin n) :
    predictableChance w π k =
      (if k ≤ π.symm k then w.rate k else 0) / w.total (remaining π k) := by
  simp [predictableChance, Weights.choice, remaining, ite_div]

lemma predictableChance_le_rate_div {n : ℕ} (w : Weights n)
    (π : Equiv.Perm (Fin n)) (k : Fin n) :
    predictableChance w π k ≤ w.rate k / w.total (remaining π k) := by
  unfold predictableChance Weights.choice
  split_ifs
  · exact le_rfl
  · exact div_nonneg (w.positive k).le (w.total_nonneg _)

/-- The clocks that survive strictly beyond time `t`. -/
noncomputable def survivorSet {n : ℕ} (times : Fin n → ℝ) (t : ℝ) :
    Finset (Fin n) := Finset.univ.filter (fun i => t < times i)

/-- The one-based rank representation in `eq:rank-representation`. -/
noncomputable def raceRank {n : ℕ} (times : Fin n → ℝ) (i : Fin n) : ℕ :=
  1 + (Finset.univ.filter fun j => times j < times i).card

/-- For distinct clocks, arrivals before `i`, survivors after `i`, and `i`
partition the labels. -/
lemma raceRank_add_survivors {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) (i : Fin n) :
    raceRank times i + (survivorSet times (times i)).card = n := by
  classical
  have hpartition :
      (Finset.univ.filter fun j => times j < times i) ∪
        survivorSet times (times i) = Finset.univ.erase i := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      survivorSet, Finset.mem_erase]
    constructor
    · intro h
      exact ⟨fun hji => by subst j; rcases h with h | h <;> exact (lt_irrefl _ h), trivial⟩
    · rintro ⟨hji, _⟩
      exact lt_or_gt_of_ne (fun h => hji (hinj h))
  have hd : Disjoint (Finset.univ.filter fun j => times j < times i)
      (survivorSet times (times i)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact (lt_asymm (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2)
  have hc := congrArg Finset.card hpartition
  rw [Finset.card_union_of_disjoint hd] at hc
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin] at hc
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  unfold raceRank
  omega

lemma raceRank_eq_iff_survivors {n : ℕ} (times : Fin n → ℝ)
    (hinj : Function.Injective times) (i : Fin n) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    raceRank times i = k ↔ (survivorSet times (times i)).card = n - k := by
  have he := raceRank_add_survivors times hinj i
  omega

end Luce



