import Luce.Section5FiniteInsertion

/-!
# Section 5: adding a predecessor to an insertion path

This proves `fixed_points.tex:1139–1151`. A new predecessor gives a longer
distinct-source path. A predecessor already in the source tuple contributes
at most one extra factor, and there are exactly `m` possible repeated labels.
The extra predecessor may equal the separately appended endpoint; the source
expression still requires all original intermediate vertices to avoid it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

/-- Product along an ordered source tuple ending at `v`. -/
def insertionPathWeight {α : Type*} {m : ℕ} (p : α → α → ℝ≥0∞)
    (v : α) (u : Fin m → α) : ℝ≥0∞ :=
  ∏ a, p (u a) ((Fin.snoc u v : Fin (m + 1) → α) a.succ)

/-- Sum over all distinct-source paths, without a restriction on the endpoint. -/
def insertionPathSum {α : Type*} [Fintype α] [DecidableEq α] (p : α → α → ℝ≥0∞)
    (m : ℕ) (v : α) : ℝ≥0∞ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin m → α => Function.Injective u),
    insertionPathWeight p v u

lemma insertionPathWeight_cons {α : Type*} {m : ℕ} (p : α → α → ℝ≥0∞)
    (v k : α) (u : Fin m → α) :
    insertionPathWeight p v (Fin.cons k u) =
      p k ((Fin.snoc u v : Fin (m + 1) → α) 0) * insertionPathWeight p v u := by
  unfold insertionPathWeight
  rw [Fin.prod_univ_succ]
  simp only [← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ]

/-- The new-label part of the predecessor sum is exactly the next path sum.
`Fin.consEquiv` proves the bijection and prevents any multiplicity loss. -/
lemma insertionPathSum_succ {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → α → ℝ≥0∞) (m : ℕ) (v : α) :
    insertionPathSum p (m + 1) v =
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → α => Function.Injective u),
        ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range u),
          p k ((Fin.snoc u v : Fin (m + 1) → α) 0) * insertionPathWeight p v u := by
  classical
  unfold insertionPathSum
  rw [Finset.sum_filter]
  calc
    _ = ∑ ku : α × (Fin m → α),
        if Function.Injective (Fin.cons ku.1 ku.2 : Fin (m + 1) → α)
        then insertionPathWeight p v (Fin.cons ku.1 ku.2) else 0 := by
      symm
      exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => α)) _ _
        (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_filter]
      by_cases hu : Function.Injective u
      · simp only [Fin.cons_injective_iff, hu, and_true, if_true]
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> simp [insertionPathWeight_cons]
      · simp [Fin.cons_injective_iff, hu]

/-- Splitting a column into new and repeated source labels. Nonnegativity is
provided by ENNReal and the repeated factors are bounded by `1`. -/
lemma insertionColumn_le_new_add_length {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (p : α → α → ℝ≥0∞) (hp : ∀ i j, p i j ≤ 1)
    (u : Fin m → α) (hu : Function.Injective u) (j : α) :
    (∑ k, p k j) ≤
      (∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range u), p k j) + m := by
  classical
  have hc : (Finset.univ.filter (fun k => k ∈ Set.range u)).card = m := by
    have he : Finset.univ.filter (fun k => k ∈ Set.range u) = Finset.univ.image u := by
      ext k
      simp
    rw [he, Finset.card_image_of_injective _ hu]
    simp
  have hh : (∑ k ∈ Finset.univ.filter (fun k => k ∈ Set.range u), p k j) ≤
      (m : ℝ≥0∞) := by
    calc
      _ ≤ ∑ _k ∈ Finset.univ.filter (fun k => k ∈ Set.range u), (1 : ℝ≥0∞) :=
        Finset.sum_le_sum (fun k _ => hp k j)
      _ = _ := by simp only [Finset.sum_const, nsmul_one, hc]
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (fun k => k ∉ Set.range u)]
  exact add_le_add le_rfl (by simpa only [not_not] using hh)

/-- Deterministic added-predecessor estimate. The two terms explicitly
account for new predecessors and each of the `m` possible collisions. -/
theorem insertion_added_predecessor_le {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → α → ℝ≥0∞) (hp : ∀ i j, p i j ≤ 1) (m : ℕ) (v : α) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin m → α => Function.Injective u),
      (∑ k, p k ((Fin.snoc u v : Fin (m + 1) → α) 0)) *
        insertionPathWeight p v u) ≤
      insertionPathSum p (m + 1) v + m * insertionPathSum p m v := by
  calc
    _ ≤ ∑ u ∈ Finset.univ.filter (fun u : Fin m → α => Function.Injective u),
        ((∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range u),
          p k ((Fin.snoc u v : Fin (m + 1) → α) 0)) + m) *
          insertionPathWeight p v u := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul' (insertionColumn_le_new_add_length p hp u
        (Finset.mem_filter.mp hu).2 _) le_rfl
    _ = insertionPathSum p (m + 1) v + m * insertionPathSum p m v := by
      simp_rw [add_mul, Finset.sum_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← insertionPathSum_succ]
      rfl

/-- The paper's `c_j = ∑_k p_(k,j)`, with extended nonnegative values. -/
def ghostColumnKernel {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (j : Fin n) : ℝ≥0∞ :=
  ∑ k, ghostOrderKernel w ell old k j

/-- The actual real column sum `c_j`, with the manuscript's orientation. -/
def ghostColumn {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ k, ghostEntry w ell old k j

/-- The precise source-restricted sum in `eq:added-predecessor`, with `m`
intermediate vertices. For `m=0`, its first target is the endpoint `v`. -/
def ghostPredecessorSum {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n =>
      Function.Injective u ∧ ∀ a, u a ≠ v),
    ghostColumnKernel w ell old ((Fin.snoc u v : Fin (m + 1) → Fin n) 0) *
      insertionPathWeight (ghostOrderKernel w ell old) v u

/-- The collision/new-label bound retains the original restriction in its
left side. Removing avoidance of `v` is explicitly justified by positivity. -/
theorem ghostPredecessorSum_le {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) :
    ghostPredecessorSum (m := m) w ell v old ≤
      ghostPathSum (m := m + 1) w ell v old + m * ghostPathSum (m := m) w ell v old := by
  calc
    _ ≤ ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        (∑ k, ghostOrderKernel w ell old k
          ((Fin.snoc u v : Fin (m + 1) → Fin n) 0)) *
            insertionPathWeight (ghostOrderKernel w ell old) v u := by
      apply Finset.sum_le_sum_of_subset
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.1⟩
    _ ≤ _ := by
      simpa only [insertionPathSum, insertionPathWeight, ghostPathSum] using
        insertion_added_predecessor_le (ghostOrderKernel w ell old)
          (ghostOrderKernel_le_one w ell old) m v

/-- The explicit constant from the two cases of the source proof. -/
def predecessorConstant (ell m : ℕ) : ℕ :=
  (2 * (ell + (m + 1) + 2) + 1) ^ (m + 1) + m * (2 * (ell + m + 2) + 1) ^ m

/-- The added-predecessor expectation, before conversion to real values.
Uniformity over n, all positive rates, and the endpoint is explicit. -/
theorem added_predecessor_ennreal {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) :
    (∫⁻ old, ghostPredecessorSum (m := m) w ell v old ∂exponentialRace w) ≤
      (predecessorConstant ell m : ℝ≥0∞) := by
  calc
    _ ≤ ∫⁻ old, ghostPathSum (m := m + 1) w ell v old +
        m * ghostPathSum (m := m) w ell v old ∂exponentialRace w :=
      lintegral_mono (ghostPredecessorSum_le w ell v)
    _ = (∫⁻ old, ghostPathSum (m := m + 1) w ell v old ∂exponentialRace w) +
        m * ∫⁻ old, ghostPathSum (m := m) w ell v old ∂exponentialRace w := by
      rw [lintegral_add_left' (aemeasurable_ghostPathSum w ell v),
        lintegral_const_mul'' _ (aemeasurable_ghostPathSum w ell v)]
    _ ≤ ((2 * (ell + (m + 1) + 2) + 1) ^ (m + 1) : ℕ) +
        (m : ℝ≥0∞) * ((2 * (ell + m + 2) + 1) ^ m : ℕ) := by
      exact add_le_add (finite_insertion_path_ennreal (m := m + 1) w ell v)
        (mul_le_mul' le_rfl (finite_insertion_path_ennreal (m := m) w ell v))
    _ = _ := by simp only [predecessorConstant, Nat.cast_add, Nat.cast_mul]

lemma aemeasurable_ghostPredecessorSum {n m : ℕ} (w : Weights n)
    (ell : ℕ) (v : Fin n) :
    AEMeasurable (ghostPredecessorSum (m := m) w ell v) (exponentialRace w) := by
  unfold ghostPredecessorSum ghostColumnKernel insertionPathWeight
  exact Finset.aemeasurable_fun_sum _ (fun u _ =>
    (Finset.aemeasurable_fun_sum _ (fun k _ => aemeasurable_ghostOrderKernel w ell _ _)).mul
      (Finset.aemeasurable_fun_prod _ (fun a _ => aemeasurable_ghostOrderKernel w ell _ _)))

lemma ghostColumnKernel_ne_top {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (j : Fin n) : ghostColumnKernel w ell old j ≠ ⊤ := by
  apply ne_of_lt
  exact ENNReal.sum_lt_top.mpr (fun k _ =>
    (ghostOrderKernel_le_one w ell old k j).trans_lt (by simp))

lemma ghostPredecessorSum_ne_top {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) : ghostPredecessorSum (m := m) w ell v old ≠ ⊤ := by
  apply ne_of_lt
  apply lt_of_le_of_lt (ghostPredecessorSum_le w ell v old)
  exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr (ghostPathSum_ne_top w ell v old),
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (lt_top_iff_ne_top.mpr
      (ghostPathSum_ne_top w ell v old))⟩

lemma ghostColumnKernel_toReal {n : ℕ} (w : Weights n) (ell : ℕ)
    (old : Fin n → ℝ) (j : Fin n) :
    (ghostColumnKernel w ell old j).toReal = ghostColumn w ell old j := by
  unfold ghostColumnKernel ghostColumn ghostEntry
  exact ENNReal.toReal_sum (fun k _ =>
    ne_of_lt ((ghostOrderKernel_le_one w ell old k j).trans_lt (by simp)))

lemma ghostPredecessorSum_toReal {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) :
    (ghostPredecessorSum (m := m) w ell v old).toReal =
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        ghostColumn w ell old ((Fin.snoc u v : Fin (m + 1) → Fin n) 0) *
          ∏ a, ghostEntry w ell old (u a)
            ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ) := by
  unfold ghostPredecessorSum
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, ghostColumnKernel_toReal,
      insertionPathWeight, ENNReal.toReal_prod, ghostEntry]
  · intro u _
    exact ENNReal.mul_ne_top (ghostColumnKernel_ne_top w ell old _) (ne_of_lt
      (ENNReal.prod_lt_top (fun a _ =>
        (ghostOrderKernel_le_one w ell old _ _).trans_lt (by simp))))

/-- Integrability of the exact source expression, not an assumed expectation. -/
theorem added_predecessor_integrable {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) :
    Integrable (fun old =>
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        ghostColumn w ell old ((Fin.snoc u v : Fin (m + 1) → Fin n) 0) *
          ∏ a, ghostEntry w ell old (u a)
            ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)) (exponentialRace w) := by
  have hf : (∫⁻ old, ghostPredecessorSum (m := m) w ell v old ∂exponentialRace w) ≠ ⊤ :=
    ne_of_lt ((added_predecessor_ennreal (m := m) w ell v).trans_lt
      (ENNReal.natCast_lt_top _))
  simpa only [ghostPredecessorSum_toReal] using
    integrable_toReal_of_lintegral_ne_top (aemeasurable_ghostPredecessorSum w ell v) hf

/-- Equation (added-predecessor), with exactly the paper's column sums and
path products. Set ell=m+1 for its cycle-length convention. -/
theorem added_predecessor {n m : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) :
    (∫ old,
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n =>
          Function.Injective u ∧ ∀ a, u a ≠ v),
        ghostColumn w ell old ((Fin.snoc u v : Fin (m + 1) → Fin n) 0) *
          ∏ a, ghostEntry w ell old (u a)
            ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
      ∂exponentialRace w) ≤ (predecessorConstant ell m : ℝ) := by
  simp_rw [← ghostPredecessorSum_toReal]
  rw [integral_toReal (aemeasurable_ghostPredecessorSum w ell v)
    (Filter.Eventually.of_forall fun old => lt_top_iff_ne_top.mpr
      (ghostPredecessorSum_ne_top w ell v old))]
  have hf : (∫⁻ old, ghostPredecessorSum (m := m) w ell v old ∂exponentialRace w) ≠ ⊤ :=
    ne_of_lt ((added_predecessor_ennreal (m := m) w ell v).trans_lt
      (ENNReal.natCast_lt_top _))
  have hh := (ENNReal.toReal_le_toReal hf (ENNReal.natCast_ne_top _)).mpr
    (added_predecessor_ennreal (m := m) w ell v)
  simpa only [ENNReal.toReal_natCast] using hh

/-- The empty intermediate path is precisely the column sum at `v`, the
singleton-cycle convention required at source line 1150. -/
lemma ghostPredecessorSum_zero {n : ℕ} (w : Weights n) (ell : ℕ)
    (v : Fin n) (old : Fin n → ℝ) :
    ghostPredecessorSum (m := 0) w ell v old = ghostColumnKernel w ell old v := by
  simp [ghostPredecessorSum, insertionPathWeight, Fin.snoc_zero, Function.Injective]

theorem ghostColumn_integrable {n : ℕ} (w : Weights n) (ell : ℕ) (v : Fin n) :
    Integrable (fun old => ghostColumn w ell old v) (exponentialRace w) := by
  simpa [Fin.snoc_zero, Function.Injective] using
    added_predecessor_integrable (m := 0) w ell v

/-- The `ell=1` source interpretation is an actual finite bound for E c_v. -/
theorem ghostColumn_expectation_le {n : ℕ} (w : Weights n) (ell : ℕ) (v : Fin n) :
    (∫ old, ghostColumn w ell old v ∂exponentialRace w) ≤
      (2 * (ell + 1 + 2) + 1 : ℕ) := by
  simpa [Fin.snoc_zero, Function.Injective, predecessorConstant] using
    added_predecessor (m := 0) w ell v

end Luce
