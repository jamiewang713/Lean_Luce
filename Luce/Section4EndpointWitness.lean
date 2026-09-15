import Luce.Section4Endpoint

/-! # Endpoint bounds with the original rate constant retained

Source: `fixed_points.tex:858–875`. The exponent in `eq:tail-epsilon`
uses the specified lower rate γ, uniformly for all sufficiently small ε.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Luce

/-- The size side condition in `prop:endpoint-bound` already forces the
terminal window to fit inside the row. Thus the indexing premise of
`section4_endpoint_bound` imposes no additional mathematical restriction. -/
lemma endpoint_window_le_row_of_size_condition {N M : ℕ} (hM : 1 ≤ M)
    (hBM : (M : ℝ) ≤ (Real.sqrt ((N : ℝ) * M) - 1) / 2) : M ≤ N := by
  by_contra hMN
  have hNM : (N : ℝ) ≤ M := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hMN))
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hsqrt : Real.sqrt ((N : ℝ) * M) ≤ M := by
    apply (Real.sqrt_le_left hM0).mpr
    nlinarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  linarith

/-- The source's closed terminal-neighborhood condition supplies the exact
rounded terminal labels, retaining its original γ. Shrinking ε₀ is harmless. -/
lemma eventually_terminal_rates_of_endpoint_witness
    (w : WeightArray) {γ ε₀ : ℝ} {n₀ : ℕ}
    (hε₀ : 0 < ε₀)
    (hrate : ∀ n : ℕ, n₀ ≤ n → ∀ k : Fin n,
      (1 - ε₀) * (n : ℝ) ≤ (k.val : ℝ) + 1 → γ ≤ (w n).rate k) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ m ∈ Finset.Icc 1 ⌈ε₁ * (n + 1)⌉₊,
        γ ≤ (w (n + 1)).rate (terminalCandidate n m) := by
  let ε₁ : ℝ := min ε₀ (1 / 2)
  have hε₁ : 0 < ε₁ := lt_min hε₀ (by norm_num)
  have hε₁ε₀ : ε₁ ≤ ε₀ := min_le_left _ _
  have hε₁one : ε₁ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  refine ⟨ε₁, hε₁, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  intro m hm
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hceil_le : ⌈ε₁ * (n + 1)⌉₊ ≤ n + 1 := by
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_add, Nat.cast_one] using
      mul_le_of_le_one_left hN.le hε₁one
  have hmn : m ≤ n + 1 := (Finset.mem_Icc.mp hm).2.trans hceil_le
  have hindex : ((terminalCandidate n m).val : ℝ) + (m : ℝ) = (n : ℝ) + 1 := by
    exact_mod_cast terminalCandidate_val_add (Finset.mem_Icc.mp hm).1 hmn
  have hm_lt : (m : ℝ) < ε₁ * (n + 1) + 1 :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans_lt
      (Nat.ceil_lt_add_one (mul_nonneg hε₁.le hN.le))
  apply hrate (n + 1) (hn.trans (Nat.le_succ n)) (terminalCandidate n m)
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith [mul_le_mul_of_nonneg_right hε₁ε₀ hN.le]

/-- Equation `eq:tail-epsilon`, retaining any specified admissible γ in the
constant and exponent. The clocks may live on arbitrary row probability spaces. -/
theorem section4_tail_expectation_bound_of_endpoint_witness
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (w : WeightArray) (hnorm : NormalizedWeights w)
    (γ ε₀ : ℝ) (n₀ : ℕ) (hγ : 0 < γ) (hε₀ : 0 < ε₀)
    (hrate : ∀ n : ℕ, n₀ ≤ n → ∀ k : Fin n,
      (1 - ε₀) * (n : ℝ) ≤ (k.val : ℝ) + 1 → γ ≤ (w n).rate k)
    (E : (n : ℕ) → Fin n → Ω n → ℝ)
    (hLaw : ∀ n i, HasLaw (E n i) (expMeasure ((w n).rate i)) (P n))
    (hIndependent : ∀ n, iIndepFun (E n) (P n)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      limsup (fun n => ∫ ω,
        (tailFixedPointCount (fun i => E n i ω) (1 - ε) : ℝ) ∂P n) atTop ≤
        (2 : ℝ) ^ (1 + γ / 2) * ε ^ (γ / 4) := by
  obtain ⟨ε₁, hε₁, hterminal⟩ :=
    eventually_terminal_rates_of_endpoint_witness w hε₀ hrate
  obtain ⟨δ, hδ, hb⟩ := endpoint_epsilon_estimate (fun n => w (n + 1))
    hnorm.sum_rates_succ hγ hε₁ hterminal
  refine ⟨min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro ε hε hεδ
  have heq (n : ℕ) :
      (∫ ω, (tailFixedPointCount (fun i => E (n + 1) i ω) (1 - ε) : ℝ) ∂P (n + 1)) =
        epsilonTailExpectation (fun n => w (n + 1)) ε n := by
    rw [tailFixedPointCount_expectation_eq _ _ _ (hLaw (n + 1)) (hIndependent (n + 1))]
    simp only [tailFixedPointCount_eq_terminalFixedPointCount n _ hε
      (hεδ.trans_le (min_le_right _ _)), epsilonTailExpectation]
  have h := hb ε hε (hεδ.trans_le (min_le_left _ _))
  have hseq : epsilonTailExpectation (fun n => w (n + 1)) ε =
      (fun n => ∫ ω,
        (tailFixedPointCount (fun i => E (n + 1) i ω) (1 - ε) : ℝ) ∂P (n + 1)) :=
    funext fun n => (heq n).symm
  rw [hseq] at h
  rw [← limsup_nat_add (fun n => ∫ ω,
    (tailFixedPointCount (fun i => E n i ω) (1 - ε) : ℝ) ∂P n) 1]
  exact h

end Luce
