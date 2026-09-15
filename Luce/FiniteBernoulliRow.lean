import Luce.BernoulliProcess

open MeasureTheory
open scoped BigOperators

namespace Luce.BernoulliProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  (X : BernoulliProcess μ)

/-- Maximum of the individual probabilities in a finite row, with empty
maximum zero. Coincident spatial locations do not combine coefficients. -/
noncomputable def rowMaximum (Y : BernoulliProcess μ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | N + 1, ω => max (rowMaximum Y N ω) (Y.probability N ω)

lemma rowMaximum_nonneg (N : ℕ) (ω : Ω) : 0 ≤ X.rowMaximum N ω := by
  induction N with
  | zero => exact le_rfl
  | succ N ih => exact ih.trans (le_max_left _ _)

lemma measurable_rowMaximum (N : ℕ) : Measurable (X.rowMaximum N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    exact ih.max (((X.predictable N).mono (X.filtration.le N)).measurable)

lemma probability_le_rowMaximum {N k : ℕ} (hk : k < N) (ω : Ω) :
    X.probability k ω ≤ X.rowMaximum N ω := by
  induction N generalizing k with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact (ih hk).trans (le_max_left _ _)
    · exact le_max_right _ _

/-- Zero extension of a finite row. No hypothesis on the original process
after `N` is needed, and its filtration is retained exactly. -/
noncomputable def truncateAt (N : ℕ) : BernoulliProcess μ where
  filtration := X.filtration
  observation k := if k < N then X.observation k else fun _ => 0
  probability k := if k < N then X.probability k else fun _ => 0
  adapted k := by
    split_ifs
    · exact X.adapted k
    · exact stronglyMeasurable_zero
  predictable k := by
    split_ifs
    · exact X.predictable k
    · exact stronglyMeasurable_zero
  zero_one k ω := by
    split_ifs
    · exact X.zero_one k ω
    · exact Or.inl rfl
  probability_nonneg k ω := by
    split_ifs
    · exact X.probability_nonneg k ω
    · exact le_rfl
  probability_le_one k ω := by
    split_ifs
    · exact X.probability_le_one k ω
    · exact zero_le_one
  conditional_mean k := by
    split_ifs
    · exact X.conditional_mean k
    · change μ[(0 : Ω → ℝ) | X.filtration k] =ᵐ[μ] 0
      rw [condExp_zero]

lemma truncateAt_probability {N k : ℕ} (hk : k < N) (ω : Ω) :
    (X.truncateAt N).probability k ω = X.probability k ω := by
  simp only [truncateAt, if_pos hk]

lemma truncateAt_observation {N k : ℕ} (hk : k < N) (ω : Ω) :
    (X.truncateAt N).observation k ω = X.observation k ω := by
  simp only [truncateAt, if_pos hk]

lemma truncateAt_probability_le_rowMaximum (N k : ℕ) (ω : Ω) :
    (X.truncateAt N).probability k ω ≤ X.rowMaximum N ω := by
  by_cases hk : k < N
  · rw [X.truncateAt_probability hk]
    exact X.probability_le_rowMaximum hk ω
  · simpa only [truncateAt, if_neg hk] using X.rowMaximum_nonneg N ω

lemma sum_truncateAt_probability (N : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range N, (X.truncateAt N).probability k ω) =
      ∑ k ∈ Finset.range N, X.probability k ω := by
  apply Finset.sum_congr rfl
  intro k hk
  exact X.truncateAt_probability (Finset.mem_range.mp hk) ω

variable [IsProbabilityMeasure μ]

/-- On the original row's good event, zero extension and predictable
deletion preserve every observation and probability in that row. -/
lemma truncatedStop_eq_on_good {N k : ℕ} {δ K : ℝ} (ω : Ω)
    (hmax : X.rowMaximum N ω ≤ δ)
    (htotal : ∑ j ∈ Finset.range N, X.probability j ω ≤ K) (hk : k < N) :
    ((X.truncateAt N).stop δ K).observation k ω = X.observation k ω ∧
      ((X.truncateAt N).stop δ K).probability k ω = X.probability k ω := by
  classical
  have hkeep : keepTerm (fun j => (X.truncateAt N).probability j ω) δ K k := by
    apply keepTerm_of_total_le (fun j => (X.truncateAt N).probability_nonneg j ω)
      (N := N) (fun j _ => (X.truncateAt_probability_le_rowMaximum N j ω).trans hmax)
      _ hk
    rwa [X.sum_truncateAt_probability]
  constructor
  · change ({ω | keepTerm (fun j => (X.truncateAt N).probability j ω) δ K k}.indicator
      ((X.truncateAt N).observation k)) ω = X.observation k ω
    change (if keepTerm (fun j => (X.truncateAt N).probability j ω) δ K k
      then (X.truncateAt N).observation k ω else 0) = X.observation k ω
    rw [if_pos hkeep]
    exact X.truncateAt_observation hk ω
  · change stoppedProbability (fun j => (X.truncateAt N).probability j ω) δ K k = _
    rw [stoppedProbability, if_pos hkeep]
    exact X.truncateAt_probability hk ω

/-- The finite-row Laplace random variable. -/
noncomputable def laplaceRow (g : ℕ → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  Real.exp (-(∑ k ∈ Finset.range N, g k * X.observation k ω))

omit [IsProbabilityMeasure μ] in
lemma measurable_laplaceRow (g : ℕ → ℝ) (N : ℕ) : Measurable (X.laplaceRow g N) := by
  apply Measurable.exp
  apply Measurable.neg
  apply Finset.measurable_sum
  intro k _
  exact (((X.adapted k).mono (X.filtration.le (k + 1))).measurable).const_mul _

lemma laplaceRow_bounds (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (N : ℕ) (ω : Ω) :
    0 ≤ X.laplaceRow g N ω ∧ X.laplaceRow g N ω ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
  exact neg_nonpos.mpr (Finset.sum_nonneg
    (fun k _ => mul_nonneg (hg k) (X.observation_nonneg k ω)))

lemma integrable_laplaceRow (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (N : ℕ) :
    Integrable (X.laplaceRow g N) μ :=
  ⟨(X.measurable_laplaceRow g N).aestronglyMeasurable,
    HasFiniteIntegral.of_mem_Icc 0 1 (ae_of_all _ (X.laplaceRow_bounds g hg N))⟩

end Luce.BernoulliProcess
