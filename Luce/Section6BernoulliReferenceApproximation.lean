import Luce.Section6BernoulliCLT

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace Luce

theorem probability_limit_of_integral_abs_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {X : ∀ n, Ω n → ℝ} (hi : ∀ n, Integrable (X n) (μ n))
    (hl : Tendsto (fun n => ∫ ω, |X n ω| ∂μ n) atTop (𝓝 0)) :
    ConvergesInProbability μ X 0 := by
  intro ε hε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa using hl.div_const ε)
  intro n
  simp only [sub_zero]
  calc
    _ ≤ (μ n).real {ω | ε ≤ |X n ω|} :=
      measureReal_mono (fun _ (h : ε < |X n _|) => h.le) (measure_ne_top _ _)
    _ ≤ (∫ ω, |X n ω| ∂μ n)/ε := (le_div_iff₀ hε).mpr (by
      simpa only [mul_comm] using mul_meas_ge_le_integral_of_nonneg
        (ae_of_all _ fun _ => abs_nonneg _) (hi n).abs ε)

theorem integral_abs_div_tendsto_of_bounded
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) {X : ∀ n, Ω n → ℝ} {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop) {C : ℝ}
    (hb : ∀ᶠ n in atTop, (∫ ω, |X n ω| ∂μ n) ≤ C) :
    Tendsto (fun n => ∫ ω, |X n ω/s n| ∂μ n) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _) _
    (show Tendsto (fun n => C/s n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop hs)
  filter_upwards [hb,hs.eventually_gt_atTop 0] with n hn hsn
  simp only [abs_div,abs_of_pos hsn,integral_div]
  exact div_le_div_of_nonneg_right hn hsn.le

namespace BernoulliProcess

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : BernoulliProcess μ)

/-- Comparing predictable atoms with a deterministic row controls the
whole compensator in L¹ without any independence assumption. -/
theorem reference_mass_error (N : ℕ) (q : ℕ → ℝ) (v : ℝ) :
    (∫ ω, |X.cltMass N ω-v| ∂μ) ≤
      (∑ k ∈ Finset.range N, ∫ ω, |X.probability k ω-q k| ∂μ)+
        |(∑ k ∈ Finset.range N, q k)-v| := by
  have hi : Integrable (X.cltMass N) μ :=
    integrable_finsetSum _ fun k _ => X.integrable_probability k
  have he (k : ℕ) : Integrable (fun ω => |X.probability k ω-q k|) μ :=
    ((X.integrable_probability k).sub (integrable_const _)).abs
  calc
    _ ≤ ∫ ω, (∑ k ∈ Finset.range N, |X.probability k ω-q k|)+
        |(∑ k ∈ Finset.range N, q k)-v| ∂μ := by
      apply integral_mono_ae ((hi.sub (integrable_const _)).abs)
        ((integrable_finsetSum _ fun k _ => he k).add (integrable_const _))
      apply ae_of_all
      intro ω
      exact (abs_sub_le _ (∑ k ∈ Finset.range N, q k) _).trans
        (add_le_add (by rw [cltMass,← Finset.sum_sub_distrib]; exact Finset.abs_sum_le_sum_abs _ _) le_rfl)
    _ = _ := by rw [integral_add (integrable_finsetSum _ fun k _ => he k) (integrable_const _),
      integral_finsetSum _ (fun k _ => he k),integral_const]; simp

theorem reference_square_bound (N : ℕ) (q : ℕ → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∀ k, q k ≤ 1) :
    (∫ ω, X.cltSquares N ω ∂μ) ≤
      2*(∑ k ∈ Finset.range N, ∫ ω, |X.probability k ω-q k| ∂μ)+
        ∑ k ∈ Finset.range N, (q k)^2 := by
  have he (k : ℕ) : Integrable (fun ω => |X.probability k ω-q k|) μ :=
    ((X.integrable_probability k).sub (integrable_const _)).abs
  calc
    _ ≤ ∫ ω, 2*(∑ k ∈ Finset.range N, |X.probability k ω-q k|)+
        ∑ k ∈ Finset.range N, (q k)^2 ∂μ := by
      apply integral_mono_ae (X.cltSquares_integrable N)
        (((integrable_finsetSum _ fun k _ => he k).const_mul 2).add (integrable_const _))
      apply ae_of_all
      intro ω
      change (∑ k ∈ Finset.range N, (X.probability k ω)^2) ≤
        2*(∑ k ∈ Finset.range N, |X.probability k ω-q k|)+∑ k ∈ Finset.range N, (q k)^2
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k _
      have h1 := X.probability_nonneg k ω
      have h2 := X.probability_le_one k ω
      have h3 := hq0 k
      have h4 := hq1 k
      have h5 := le_abs_self (X.probability k ω-q k)
      have h6 := neg_le_abs (X.probability k ω-q k)
      by_cases hpq : X.probability k ω ≤ q k
      · nlinarith [abs_nonneg (X.probability k ω-q k)]
      · have hd : 0 ≤ X.probability k ω-q k := by linarith
        have := mul_le_mul_of_nonneg_right (show X.probability k ω+q k ≤ 2 by linarith) hd
        nlinarith
    _ = _ := by rw [integral_add ((integrable_finsetSum _ fun k _ => he k).const_mul 2)
      (integrable_const _),integral_const_mul,integral_finsetSum _ (fun k _ => he k),integral_const]; simp

end BernoulliProcess

namespace BernoulliCLT

/-- An L¹ deterministic reference row is sufficient for the adapted
Bernoulli CLT. The three bounded errors are the quantities supplied by
the fixed-cutoff critical-pole proof. -/
theorem boundedContinuous_tendsto_of_reference
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, BernoulliProcess (μ n)) (N : ℕ → ℕ) (q : ℕ → ℕ → ℝ) {v : ℕ → ℝ}
    (hv : Tendsto v atTop atTop) (hq0 : ∀ n k, 0 ≤ q n k) (hq1 : ∀ n k, q n k ≤ 1)
    {C : ℝ} (herr : ∀ᶠ n in atTop,
      (∑ k ∈ Finset.range (N n), ∫ ω, |(X n).probability k ω-q n k| ∂μ n) ≤ C ∧
      |(∑ k ∈ Finset.range (N n), q n k)-v n| ≤ C ∧
      (∑ k ∈ Finset.range (N n), (q n k)^2) ≤ C)
    (F : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (((X n).cltCount (N n) ω-v n)/Real.sqrt (v n)) ∂μ n)
      atTop (𝓝 (∫ z, F z ∂ProbabilityTheory.gaussianReal 0 1)) := by
  have hmass : ∀ᶠ n in atTop, (∫ ω, |(X n).cltMass (N n) ω-v n| ∂μ n) ≤ 2*C := by
    filter_upwards [herr] with n hn
    exact ((X n).reference_mass_error (N n) (q n) (v n)).trans (by linarith [hn.1,hn.2.1])
  have hsquare : ∀ᶠ n in atTop, (∫ ω, |(X n).cltSquares (N n) ω| ∂μ n) ≤ 3*C := by
    filter_upwards [herr] with n hn
    simp only [abs_of_nonneg (BernoulliProcess.cltSquares_nonneg _ _ _)]
    exact ((X n).reference_square_bound (N n) (q n) (hq0 n) (hq1 n)).trans (by linarith [hn.1,hn.2.2])
  apply boundedContinuous_tendsto μ X N hv
  · apply probability_limit_of_integral_abs_tendsto μ
    · intro n
      exact ((integrable_finsetSum _ fun k _ => (X n).integrable_probability k).sub
        (integrable_const (v n))).div_const _
    · exact integral_abs_div_tendsto_of_bounded μ (Real.tendsto_sqrt_atTop.comp hv) hmass
  · apply probability_limit_of_integral_abs_tendsto μ
    · intro n
      exact ((X n).cltSquares_integrable (N n)).div_const _
    · exact integral_abs_div_tendsto_of_bounded μ hv hsquare

/-- Eventual bounds on the reference row are enough; finitely many
initial rows do not affect the normal limit. -/
theorem boundedContinuous_tendsto_of_eventual_reference
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, BernoulliProcess (μ n)) (N : ℕ → ℕ) (q : ℕ → ℕ → ℝ) {v : ℕ → ℝ}
    (hv : Tendsto v atTop atTop)
    (hq : ∀ᶠ n in atTop, ∀ k, 0 ≤ q n k ∧ q n k ≤ 1)
    {C : ℝ} (herr : ∀ᶠ n in atTop,
      (∑ k ∈ Finset.range (N n), ∫ ω, |(X n).probability k ω-q n k| ∂μ n) ≤ C ∧
      |(∑ k ∈ Finset.range (N n), q n k)-v n| ≤ C ∧
      (∑ k ∈ Finset.range (N n), (q n k)^2) ≤ C)
    (F : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (((X n).cltCount (N n) ω-v n)/Real.sqrt (v n)) ∂μ n)
      atTop (𝓝 (∫ z, F z ∂ProbabilityTheory.gaussianReal 0 1)) := by
  classical
  let q' : ℕ → ℕ → ℝ := fun n k => if ∀ j, 0 ≤ q n j ∧ q n j ≤ 1 then q n k else 0
  apply boundedContinuous_tendsto_of_reference μ X N q' hv
  · intro n k
    dsimp [q']
    split_ifs with h
    · exact (h k).1
    · exact le_rfl
  · intro n k
    dsimp [q']
    split_ifs with h
    · exact (h k).2
    · norm_num
  · filter_upwards [hq,herr] with n hn he
    simpa only [q',if_pos hn] using he
end BernoulliCLT
end Luce
