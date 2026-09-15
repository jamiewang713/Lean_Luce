import Luce.Section5BulkCylinder

/-!
# The weighted bulk bound for every row

Source: `fixed_points.tex:1007–1013`. The asymptotic reservoir supplies a
uniform constant after a finite threshold. Strict positivity of every
finite-row weight lets us absorb the earlier rows into the same constant.
Thus the source's bound has no omitted initial rows.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Luce
attribute [local instance] Classical.propDecidable

/-- A finite constant controlling every early-row source tuple. The extra
one handles the empty tuple and keeps the resulting bound positive. -/
def earlyBulkCylinderConstant (w : WeightArray) (r N : ℕ) : ℝ :=
  1 + ∑ m : Fin N, ∑ i : Fin r ↪ Fin m.val,
    (m.val : ℝ) ^ r / ∏ a, (w m.val).rate (i a)

lemma earlyBulkCylinderConstant_one_le (w : WeightArray) (r N : ℕ) :
    1 ≤ earlyBulkCylinderConstant w r N := by
  unfold earlyBulkCylinderConstant
  have hs : 0 ≤ ∑ m : Fin N, ∑ i : Fin r ↪ Fin m.val,
      (m.val : ℝ) ^ r / ∏ a, (w m.val).rate (i a) := by
    apply Finset.sum_nonneg
    intro m _
    apply Finset.sum_nonneg
    intro i _
    exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (Finset.prod_nonneg fun a _ => ((w m.val).positive (i a)).le)
  linarith

lemma earlyBulkCylinderConstant_ge (w : WeightArray) (r N n : ℕ) (hn : n < N)
    (i : Fin r ↪ Fin n) :
    (n : ℝ) ^ r / (∏ a, (w n).rate (i a)) ≤ earlyBulkCylinderConstant w r N := by
  let term := fun m : Fin N => ∑ i : Fin r ↪ Fin m.val,
    (m.val : ℝ) ^ r / ∏ a, (w m.val).rate (i a)
  have hterm (m : Fin N) (u : Fin r ↪ Fin m.val) :
      0 ≤ (m.val : ℝ) ^ r / ∏ a, (w m.val).rate (u a) :=
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (Finset.prod_nonneg fun a _ => ((w m.val).positive (u a)).le)
  have hi : (n : ℝ) ^ r / (∏ a, (w n).rate (i a)) ≤ term ⟨n, hn⟩ :=
    Finset.single_le_sum (fun u _ => hterm ⟨n, hn⟩ u) (Finset.mem_univ i)
  have htermnonneg (m : Fin N) : 0 ≤ term m :=
    Finset.sum_nonneg (fun u _ => hterm m u)
  have hn' : term ⟨n, hn⟩ ≤ ∑ m : Fin N, term m :=
    Finset.single_le_sum (f := term) (fun m _ => htermnonneg m)
      (Finset.mem_univ (⟨n, hn⟩ : Fin N))
  have h := hi.trans hn'
  change _ ≤ 1 + ∑ m : Fin N, term m
  linarith

/-- The literal weighted bulk cylinder inequality for all n. Positive
weights make the finite initial-row constants finite; n=0 and r=0 are
handled explicitly, rather than concealed by totalized division. -/
theorem ProfileLimit.weighted_bulk_cylinder_all {w : WeightArray} {f : ℝ → ℝ}
    (hf : ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      ∀ i j : Fin r ↪ Fin n,
        (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
          (exponentialRace (w n)).real
            {old | ∀ a, raceRank old (i a) = (j a).val + 1} ≤
            K / (n : ℝ) ^ r * ∏ a, (w n).rate (i a) := by
  obtain ⟨K₀, hK₀, hlarge⟩ := hf.weighted_bulk_cylinder r hα
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  let K := max K₀ (earlyBulkCylinderConstant w r N)
  have hK₀K : K₀ ≤ K := le_max_left _ _
  have hKearly : earlyBulkCylinderConstant w r N ≤ K := le_max_right _ _
  have hKone : 1 ≤ K := (earlyBulkCylinderConstant_one_le w r N).trans hKearly
  refine ⟨K, hK₀.trans_le hK₀K, ?_⟩
  intro n i j hj
  by_cases hn0 : n = 0
  · subst n
    cases r with
    | zero =>
      simp only [pow_zero, div_one, Fin.prod_univ_zero, mul_one]
      exact measureReal_le_one.trans hKone
    | succ r => exact Fin.elim0 (i 0)
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hpow : 0 < (n : ℝ) ^ r := pow_pos hnpos _
    have hprod : 0 < ∏ a, (w n).rate (i a) :=
      Finset.prod_pos (fun a _ => (w n).positive (i a))
    by_cases hnN : N ≤ n
    · apply (hN n hnN i j hj).trans
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hK₀K hpow.le) hprod.le
    · have hratio := (earlyBulkCylinderConstant_ge w r N n (lt_of_not_ge hnN) i).trans hKearly
      have hp : (n : ℝ) ^ r ≤ K * ∏ a, (w n).rate (i a) := (div_le_iff₀ hprod).mp hratio
      have hone : 1 ≤ K / (n : ℝ) ^ r * ∏ a, (w n).rate (i a) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hpow, one_mul]
        exact hp
      exact measureReal_le_one.trans hone

end Luce
