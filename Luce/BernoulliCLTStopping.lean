import Luce.BernoulliCharacteristic

/-! Removing the predictable cap in the Bernoulli central limit criterion. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace Luce.BernoulliProcess

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : BernoulliProcess μ)

theorem stop_cltMass_le (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (ω : Ω) :
    (X.stop 1 K).cltMass N ω ≤ K := X.stop_sum_probability_le_cap hK N ω

theorem stop_cltSquares_le (K : ℝ) (N : ℕ) (ω : Ω) :
    (X.stop 1 K).cltSquares N ω ≤ X.cltSquares N ω := by
  apply Finset.sum_le_sum
  intro k _
  exact pow_le_pow_left₀ ((X.stop 1 K).probability_nonneg k ω)
    (stoppedProbability_le (X.probability_nonneg k ω)) 2

theorem stop_clt_eq_of_mass_le {K : ℝ} {N : ℕ} {ω : Ω}
    (hK : X.cltMass N ω ≤ K) :
    (X.stop 1 K).cltCount N ω = X.cltCount N ω ∧
      (X.stop 1 K).cltMass N ω = X.cltMass N ω := by
  have hk (k : ℕ) (hk : k < N) : keepTerm (fun j => X.probability j ω) 1 K k :=
    keepTerm_of_total_le (fun j => X.probability_nonneg j ω)
      (fun j _ => X.probability_le_one j ω) hK hk
  constructor
  · apply Finset.sum_congr rfl
    intro k hk'
    change {ω | keepTerm (fun j => X.probability j ω) 1 K k}.indicator
      (X.observation k) ω = X.observation k ω
    exact Set.indicator_of_mem (s := {ω | keepTerm (fun j => X.probability j ω) 1 K k})
      (hk k (Finset.mem_range.mp hk')) (X.observation k)
  · apply Finset.sum_congr rfl
    intro k hk'
    exact stoppedProbability_eq_of_total_le (fun j => X.probability_nonneg j ω)
      (fun j _ => X.probability_le_one j ω) hK (Finset.mem_range.mp hk')

end Luce.BernoulliProcess

namespace Luce.BernoulliCLT

theorem relative_mass_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {A : ∀ n, Ω n → ℝ} {v : ℕ → ℝ} (hv : ∀ n, 1 ≤ v n)
    (hA : ConvergesInProbability μ (fun n ω => (A n ω-v n)/Real.sqrt (v n)) 0) :
    ConvergesInProbability μ (fun n ω => A n ω/v n) 1 := by
  apply hA.mono
  intro n ω
  have hv0 : 0 < v n := lt_of_lt_of_le zero_lt_one (hv n)
  have hs : 0 < Real.sqrt (v n) := Real.sqrt_pos.mpr hv0
  have hs1 : 1 ≤ Real.sqrt (v n) := Real.one_le_sqrt.mpr (hv n)
  have he : A n ω/v n - 1 = ((A n ω-v n)/Real.sqrt (v n))/Real.sqrt (v n) := by
    rw [div_div, Real.mul_self_sqrt hv0.le]
    field_simp
  rw [he, sub_zero, abs_div, abs_of_pos hs]
  exact div_le_self (abs_nonneg _) hs1

theorem mass_cap_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {A : ∀ n, Ω n → ℝ} {v : ℕ → ℝ} (hv : ∀ n, 1 ≤ v n)
    (hA : ConvergesInProbability μ (fun n ω => (A n ω-v n)/Real.sqrt (v n)) 0) :
    Tendsto (fun n => (μ n).real {ω | 2*v n < A n ω}) atTop (𝓝 0) := by
  have ht := (relative_mass_probability μ hv hA).upper_tail (K := 2) (by norm_num)
  convert ht using 1
  ext n
  congr 1
  ext ω
  exact (lt_div_iff₀ (lt_of_lt_of_le zero_lt_one (hv n))).symm

end Luce.BernoulliCLT
