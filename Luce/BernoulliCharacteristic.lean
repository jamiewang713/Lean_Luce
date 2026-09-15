import Luce.BernoulliCharacteristicEstimates
import Luce.FiniteAdaptedBernoulli

/-! Finite-row characteristic-function estimates, using only adaptation. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Luce.BernoulliProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] (X : BernoulliProcess μ)

def cltCount (N : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.range N, X.observation k ω
def cltMass (N : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.range N, X.probability k ω
def cltSquares (N : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.range N, (X.probability k ω)^2

omit [IsProbabilityMeasure μ] in
theorem cltCount_measurable (N : ℕ) : Measurable (X.cltCount N) := by
  exact Finset.measurable_sum _ fun k _ =>
    ((X.adapted k).mono (X.filtration.le (k+1))).measurable

omit [IsProbabilityMeasure μ] in
theorem cltMass_measurable (N : ℕ) : Measurable (X.cltMass N) := by
  exact Finset.measurable_sum _ fun k _ =>
    ((X.predictable k).mono (X.filtration.le k)).measurable

omit [IsProbabilityMeasure μ] in
theorem cltSquares_measurable (N : ℕ) : Measurable (X.cltSquares N) := by
  exact Finset.measurable_sum _ fun k _ =>
    (((X.predictable k).mono (X.filtration.le k)).measurable.pow_const 2)

omit [IsProbabilityMeasure μ] in
theorem cltMass_nonneg (N : ℕ) (ω : Ω) : 0 ≤ X.cltMass N ω :=
  Finset.sum_nonneg fun k _ => X.probability_nonneg k ω

omit [IsProbabilityMeasure μ] in
theorem cltSquares_nonneg (N : ℕ) (ω : Ω) : 0 ≤ X.cltSquares N ω :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [IsProbabilityMeasure μ] in
theorem cltSquares_le_mass (N : ℕ) (ω : Ω) : X.cltSquares N ω ≤ X.cltMass N ω := by
  apply Finset.sum_le_sum
  intro k _
  nlinarith [X.probability_nonneg k ω, X.probability_le_one k ω]

omit [IsProbabilityMeasure μ] in
theorem cltMass_mono {m N : ℕ} (hm : m ≤ N) (ω : Ω) :
    X.cltMass m ω ≤ X.cltMass N ω :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
    (fun k _ _ => X.probability_nonneg k ω)

theorem cltSquares_integrable (N : ℕ) : Integrable (X.cltSquares N) μ := by
  apply integrable_finsetSum
  intro k _
  simpa only [pow_two] using (X.integrable_probability k).mul_bdd
    ((X.predictable k).mono (X.filtration.le k)).aestronglyMeasurable
    (ae_of_all μ fun ω => by simpa [abs_of_nonneg (X.probability_nonneg k ω)]
      using X.probability_le_one k ω)

def characteristicCompensation (u : ℝ) (N : ℕ) (ω : Ω) : ℂ :=
  Complex.exp ((u : ℂ) * Complex.I * X.cltCount N ω -
    BernoulliCLT.coefficient u * X.cltMass N ω)

omit [IsProbabilityMeasure μ] in
theorem characteristicCompensation_adapted (u : ℝ) (N : ℕ) :
    StronglyMeasurable[X.filtration N] (X.characteristicCompensation u N) := by
  have hS : Measurable[X.filtration N] (X.cltCount N) := by
    apply Finset.measurable_sum
    intro k hk
    exact ((X.adapted k).mono (X.filtration.mono (Nat.succ_le_of_lt
      (Finset.mem_range.mp hk)))).measurable
  have hA : Measurable[X.filtration N] (X.cltMass N) := by
    apply Finset.measurable_sum
    intro k hk
    exact ((X.predictable k).mono (X.filtration.mono
      (Nat.le_of_lt (Finset.mem_range.mp hk)))).measurable
  unfold characteristicCompensation
  exact (Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp hS).const_mul _ |>.sub
      ((Complex.measurable_ofReal.comp hA).const_mul _))).stronglyMeasurable

omit [IsProbabilityMeasure μ] in
theorem characteristicCompensation_norm (u : ℝ) (N : ℕ) (ω : Ω) :
    ‖X.characteristicCompensation u N ω‖ =
      Real.exp (-(BernoulliCLT.coefficient u).re * X.cltMass N ω) := by
  simp [characteristicCompensation, Complex.norm_exp]

omit [IsProbabilityMeasure μ] in
theorem characteristicCompensation_bound (u : ℝ) {N : ℕ} {K : ℝ}
    (hK : ∀ ω, X.cltMass N ω ≤ K) {m : ℕ} (hm : m ≤ N) (ω : Ω) :
    ‖X.characteristicCompensation u m ω‖ ≤
      Real.exp (-(BernoulliCLT.coefficient u).re * K) := by
  rw [X.characteristicCompensation_norm]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left ((X.cltMass_mono hm ω).trans (hK ω))
    (neg_nonneg.mpr (BernoulliCLT.coefficient_re_nonpos u))

theorem characteristicCompensation_integrable (u : ℝ) (N : ℕ) :
    Integrable (X.characteristicCompensation u N) μ := by
  apply Integrable.mono' (integrable_const (Real.exp
    (-(BernoulliCLT.coefficient u).re * N)))
    ((X.characteristicCompensation_adapted u N).mono (X.filtration.le N)).aestronglyMeasurable
  apply ae_of_all
  apply X.characteristicCompensation_bound u (N := N) _ le_rfl
  intro ω
  calc
    X.cltMass N ω ≤ ∑ k ∈ Finset.range N, (1 : ℝ) :=
      Finset.sum_le_sum fun k _ => X.probability_le_one k ω
    _ = N := by simp

theorem integrable_observation_smul {H : Ω → ℂ} (hH : Integrable H μ) (k : ℕ) :
    Integrable (fun ω => X.observation k ω • H ω) μ := by
  apply hH.norm.mono'
    (((X.adapted k).mono (X.filtration.le (k+1))).aestronglyMeasurable.smul
      hH.aestronglyMeasurable)
  apply ae_of_all
  intro ω
  change ‖X.observation k ω • H ω‖ ≤ ‖H ω‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (X.observation_nonneg k ω)]
  exact mul_le_of_le_one_left (norm_nonneg _) (X.observation_le_one k ω)

omit [IsProbabilityMeasure μ] in
theorem integrable_probability_smul {H : Ω → ℂ} (hH : Integrable H μ) (k : ℕ) :
    Integrable (fun ω => X.probability k ω • H ω) μ := by
  apply hH.norm.mono'
    (((X.predictable k).mono (X.filtration.le k)).aestronglyMeasurable.smul
      hH.aestronglyMeasurable)
  apply ae_of_all
  intro ω
  change ‖X.probability k ω • H ω‖ ≤ ‖H ω‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (X.probability_nonneg k ω)]
  exact mul_le_of_le_one_left (norm_nonneg _) (X.probability_le_one k ω)

theorem integral_predictable_observation_smul {H : Ω → ℂ} (k : ℕ)
    (hH : StronglyMeasurable[X.filtration k] H) (hi : Integrable H μ) :
    (∫ ω, X.observation k ω • H ω ∂μ) = ∫ ω, X.probability k ω • H ω ∂μ := by
  rw [← integral_condExp (X.filtration.le k)]
  apply integral_congr_ae
  have h := condExp_smul_of_aestronglyMeasurable_right
    (X.integrable_observation k) (X.integrable_observation_smul hi k) hH.aestronglyMeasurable
  filter_upwards [h, X.conditional_mean k] with ω hω hp
  change μ[(fun ω => X.observation k ω • H ω) | X.filtration k] ω =
    μ[X.observation k | X.filtration k] ω • H ω at hω
  rw [hp] at hω
  exact hω

theorem integral_bernoulli_affine {H : Ω → ℂ} (k : ℕ)
    (hH : StronglyMeasurable[X.filtration k] H) (hi : Integrable H μ) (a : ℂ) :
    (∫ ω, H ω * (1 + a * X.observation k ω) ∂μ) =
      ∫ ω, H ω * (1 + a * X.probability k ω) ∂μ := by
  have he (b : ℝ) (z : ℂ) : z * (1 + a * b) = z + a * (b • z) := by
    simp only [Complex.real_smul]
    ring
  simp_rw [he]
  rw [integral_add hi ((X.integrable_observation_smul hi k).const_mul a),
    integral_add hi ((X.integrable_probability_smul hi k).const_mul a),
    integral_const_mul, integral_const_mul,
    X.integral_predictable_observation_smul k hH hi]

omit [IsProbabilityMeasure μ] in
theorem characteristicCompensation_succ (u : ℝ) (k : ℕ) (ω : Ω) :
    X.characteristicCompensation u (k+1) ω =
      X.characteristicCompensation u k ω *
      Complex.exp (-BernoulliCLT.coefficient u * X.probability k ω) *
      (1 + BernoulliCLT.coefficient u * X.observation k ω) := by
  have he : Complex.exp ((u : ℂ) * Complex.I * X.observation k ω) =
      1 + BernoulliCLT.coefficient u * X.observation k ω := by
    rcases X.zero_one k ω with h | h <;> simp [h, BernoulliCLT.coefficient]
  rw [← he]
  unfold characteristicCompensation
  rw [← Complex.exp_add, ← Complex.exp_add]
  unfold cltCount cltMass
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  congr 1
  ring

theorem integrable_compensation_prefactor (u : ℝ) (k : ℕ) :
    Integrable (fun ω => X.characteristicCompensation u k ω *
      Complex.exp (-BernoulliCLT.coefficient u * X.probability k ω)) μ := by
  apply (X.characteristicCompensation_integrable u k).mul_bdd
  · have hp := ((X.predictable k).mono (X.filtration.le k)).measurable
    exact (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp hp).const_mul _)).aestronglyMeasurable
  · apply ae_of_all
    intro ω
    calc
      ‖Complex.exp (-BernoulliCLT.coefficient u * X.probability k ω)‖ ≤
          Real.exp ‖-BernoulliCLT.coefficient u * X.probability k ω‖ :=
        Complex.norm_exp_le_exp_norm _
      _ ≤ Real.exp ‖BernoulliCLT.coefficient u‖ := by
        apply Real.exp_le_exp.mpr
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (X.probability_nonneg k ω)]
        exact mul_le_of_le_one_right (norm_nonneg _) (X.probability_le_one k ω)

theorem integral_characteristicCompensation_succ (u : ℝ) (k : ℕ) :
    (∫ ω, X.characteristicCompensation u (k+1) ω ∂μ) =
      ∫ ω, X.characteristicCompensation u k ω *
        Complex.exp (-BernoulliCLT.coefficient u * X.probability k ω) *
        (1 + BernoulliCLT.coefficient u * X.probability k ω) ∂μ := by
  simp_rw [X.characteristicCompensation_succ]
  apply X.integral_bernoulli_affine k _ (X.integrable_compensation_prefactor u k)
  have hp := (X.predictable k).measurable
  have hZ := (X.characteristicCompensation_adapted u k).measurable
  exact (hZ.mul (Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp hp).const_mul _))).stronglyMeasurable

end Luce.BernoulliProcess
