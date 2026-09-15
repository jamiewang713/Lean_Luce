import Luce.Section5InteriorWindows
import Luce.Section5CycleProbability

/-!
# The row-sum estimate for cycles without high-rate vertices

Source: `fixed_points.tex:1225–1230`. The last edge is bounded by the
actual length of its finite interior window. The other edges are summed
using the proved row bound. No bound on background rates is imposed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace Luce
attribute [local instance] Classical.propDecidable

/-- An open path starting at v, with its k successive targets exposed. -/
def forwardPathWeight {α : Type*} {k : ℕ} (p : α → α → ℝ)
    (v : α) (u : Fin k → α) : ℝ :=
  ∏ a, p ((Fin.cons v u : Fin (k + 1) → α) a.castSucc) (u a)

lemma forwardPathWeight_cons {α : Type*} {k : ℕ} (p : α → α → ℝ)
    (v x : α) (u : Fin k → α) :
    forwardPathWeight p v (Fin.cons x u) = p v x * forwardPathWeight p x u := by
  simp [forwardPathWeight, Fin.prod_univ_succ]

/-- Repeated targets are included in this upper bound. Nonnegativity
justifies subsequently dropping the distinctness and rate restrictions. -/
theorem forwardPathWeight_sum_le {α : Type*} [Fintype α]
    (p : α → α → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (C : ℝ) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, p i j ≤ C)
    (k : ℕ) (v : α) :
    (∑ u : Fin k → α, forwardPathWeight p v u) ≤ C ^ k := by
  induction k generalizing v with
  | zero => simp [forwardPathWeight]
  | succ k ih =>
    calc
      _ = ∑ xu : α × (Fin k → α), forwardPathWeight p v (Fin.cons xu.1 xu.2) :=
        (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => α)) _ _
          (fun _ => rfl)).symm
      _ = ∑ x, p v x * ∑ u : Fin k → α, forwardPathWeight p x u := by
        simp only [Fintype.sum_prod_type, forwardPathWeight_cons, Finset.mul_sum]
      _ ≤ ∑ x, p v x * C ^ k :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (ih x) (hp v x))
      _ = (∑ x, p v x) * C ^ k := (Finset.sum_mul _ _ _).symm
      _ ≤ C * C ^ k := mul_le_mul_of_nonneg_right (hrow v) (pow_nonneg hC _)
      _ = C ^ (k + 1) := (pow_succ' _ _).symm

/-- A nonterminal ghost window has finite volume. This is proved before
using its real length, so `toReal` cannot turn an infinite length into zero. -/
lemma ghostWindowVolume_ne_top_of_interior {n : ℕ} (ell : ℕ)
    (old : Fin n → ℝ) (hnonneg : ∀ i, 0 ≤ old i)
    (j : Fin n) (hj : j.val + ell < n) : ghostWindowVolume ell old j ≠ ⊤ := by
  by_cases hi : Injective old
  · simp only [ghostWindowVolume, hi, dite_true]
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono (t := Ioo 0
      (arrivalTime old hi ⟨j.val + ell, hj⟩)) ?_) (by simp)
    intro t ht
    refine ⟨ghostWindowByOrder_pos old hi hnonneg ell j ht, ?_⟩
    simpa only [GhostWindowByOrder, show j.val + 1 + ell ≤ n by omega,
      dite_true] using ht.2
  · simp [ghostWindowVolume, hi]

/-- The closing-edge inequality in source 1225–1227, derived from the
literal density integral and finite length of J_j. -/
theorem ghostEntry_le_rate_mul_length {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (hnonneg : ∀ i, 0 ≤ old i)
    (i j : Fin n) (hj : j.val + ell < n) :
    ghostEntry w ell old i j ≤ w.rate i * ghostWindowLength ell old j := by
  by_cases hi : Injective old
  · let J := {t | GhostWindowByOrder old hi ell j t}
    have hfin : volume J ≠ ⊤ := by
      simpa only [ghostWindowVolume, hi, dite_true] using
        ghostWindowVolume_ne_top_of_interior ell old hnonneg j hj
    haveI : IsFiniteMeasure (volume.restrict J) := ⟨by simpa using lt_top_iff_ne_top.mpr hfin⟩
    have hInt := ghostEntry_eq_density_integral w ell old hi hnonneg i j
    rw [hInt.2]
    calc
      _ ≤ ∫ _t in J, w.rate i := by
        apply integral_mono_ae hInt.1 (integrable_const _)
        filter_upwards [ae_restrict_mem (measurableSet_ghostWindowByOrder old hi ell j)] with t ht
        apply mul_le_of_le_one_right (w.positive i).le
        apply Real.exp_le_one_iff.mpr
        have := ghostWindowByOrder_pos old hi hnonneg ell j ht
        nlinarith [w.positive i]
      _ = _ := by
        simp [integral_const, ghostWindowLength, ghostWindowVolume, hi, J,
          Measure.real, mul_comm]
  · simp [ghostEntry, ghostOrderKernel, ghostWindowLength, ghostWindowVolume, hi]

/-- Factoring the closing edge preserves the rooted tuple, including
the fixed-point case k=0. -/
lemma rootedGhostProduct_eq_forward {n k : ℕ} (w : Weights n)
    (ell : ℕ) (old : Fin n → ℝ) (v : Fin n) (u : Fin k → Fin n) :
    (∏ a : Fin (k + 1), ghostEntry w ell old
      ((Fin.cons v u : Fin (k + 1) → Fin n) a)
      ((Fin.snoc u v : Fin (k + 1) → Fin n) a)) =
    forwardPathWeight (ghostEntry w ell old) v u *
      ghostEntry w ell old ((Fin.cons v u : Fin (k + 1) → Fin n) (Fin.last k)) v := by
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, forwardPathWeight]

/-- Deterministic row summation, source 1227–1230. The finite sum retains
the exact distinct rooted tuples with all their source rates at most M. -/
theorem bounded_ghost_cycle_sum_le {n : ℕ} (w : Weights n) (k : ℕ)
    (M : ℝ) (hM : 0 ≤ M) (old : Fin n → ℝ)
    (hnonneg : ∀ i, 0 ≤ old i) (v : Fin n) (hv : v.val + (k + 1) < n) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
      Injective u ∧ (∀ a, u a ≠ v) ∧
        ∀ a, w.rate ((Fin.cons v u : Fin (k + 1) → Fin n) a) ≤ M),
      ∏ a : Fin (k + 1), ghostEntry w (k + 1) old
        ((Fin.cons v u : Fin (k + 1) → Fin n) a)
        ((Fin.snoc u v : Fin (k + 1) → Fin n) a)) ≤
      (M * ghostWindowLength (k + 1) old v) * (2 * (k + 1) + 1 : ℕ) ^ k := by
  have hp (i j : Fin n) := (ghostEntry_mem_Icc w (k + 1) old i j).1
  have hlen : 0 ≤ ghostWindowLength (k + 1) old v := ENNReal.toReal_nonneg
  calc
    _ ≤ ∑ u ∈ Finset.univ.filter (fun u : Fin k → Fin n =>
        Injective u ∧ (∀ a, u a ≠ v) ∧
          ∀ a, w.rate ((Fin.cons v u : Fin (k + 1) → Fin n) a) ≤ M),
        (M * ghostWindowLength (k + 1) old v) * forwardPathWeight (ghostEntry w (k + 1) old) v u := by
      apply Finset.sum_le_sum
      intro u hu
      rw [rootedGhostProduct_eq_forward, mul_comm]
      apply mul_le_mul_of_nonneg_right
        ((ghostEntry_le_rate_mul_length w (k + 1) old hnonneg _ v hv).trans
          (mul_le_mul_of_nonneg_right ((Finset.mem_filter.mp hu).2.2.2 _) hlen))
      exact Finset.prod_nonneg (fun a _ => hp _ _)
    _ ≤ ∑ u : Fin k → Fin n,
        (M * ghostWindowLength (k + 1) old v) * forwardPathWeight (ghostEntry w (k + 1) old) v u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun u _ _ => mul_nonneg (mul_nonneg hM hlen) (Finset.prod_nonneg (fun a _ => hp _ _)))
    _ = (M * ghostWindowLength (k + 1) old v) *
        ∑ u : Fin k → Fin n, forwardPathWeight (ghostEntry w (k + 1) old) v u :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (forwardPathWeight_sum_le _ hp _ (Nat.cast_nonneg _)
        (ghostEntry_row_bound w (k + 1) old hnonneg) k v) (mul_nonneg hM hlen)

end Luce
