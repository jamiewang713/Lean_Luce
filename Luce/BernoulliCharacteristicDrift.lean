import Luce.BernoulliCharacteristic

/-! The accumulated error of the compensated characteristic function. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace Luce.BernoulliProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] (X : BernoulliProcess μ)

theorem compensation_drift_integrable (u : ℝ) (k : ℕ) :
    Integrable (fun ω => X.characteristicCompensation u k ω *
      (Complex.exp (-BernoulliCLT.coefficient u * X.probability k ω) *
        (1 + BernoulliCLT.coefficient u * X.probability k ω) - 1)) μ := by
  let H := fun ω => X.characteristicCompensation u k ω *
    Complex.exp (-BernoulliCLT.coefficient u * X.probability k ω)
  have hi : Integrable H μ := X.integrable_compensation_prefactor u k
  have hh := (hi.add ((X.integrable_probability_smul hi k).const_mul
    (BernoulliCLT.coefficient u))).sub (X.characteristicCompensation_integrable u k)
  apply hh.congr
  apply ae_of_all
  intro ω
  dsimp [H]
  ring

theorem integral_compensation_drift (u : ℝ) (k : ℕ) :
    (∫ ω, X.characteristicCompensation u (k+1) ω ∂μ) -
      (∫ ω, X.characteristicCompensation u k ω ∂μ) =
    ∫ ω, X.characteristicCompensation u k ω *
      (Complex.exp (-BernoulliCLT.coefficient u * X.probability k ω) *
        (1 + BernoulliCLT.coefficient u * X.probability k ω) - 1) ∂μ := by
  rw [X.integral_characteristicCompensation_succ]
  have he (ω : Ω) : X.characteristicCompensation u k ω *
        Complex.exp (-BernoulliCLT.coefficient u * X.probability k ω) *
        (1 + BernoulliCLT.coefficient u * X.probability k ω) =
      X.characteristicCompensation u k ω *
        (Complex.exp (-BernoulliCLT.coefficient u * X.probability k ω) *
          (1 + BernoulliCLT.coefficient u * X.probability k ω) - 1) +
        X.characteristicCompensation u k ω := by ring
  simp_rw [he]
  rw [integral_add (X.compensation_drift_integrable u k)
    (X.characteristicCompensation_integrable u k), add_sub_cancel_right]

theorem characteristicCompensation_step_error {u K : ℝ} {N k : ℕ}
    (ha : ‖BernoulliCLT.coefficient u‖ ≤ 1)
    (hK : ∀ ω, X.cltMass N ω ≤ K) (hk : k < N) :
    ‖(∫ ω, X.characteristicCompensation u (k+1) ω ∂μ) -
      (∫ ω, X.characteristicCompensation u k ω ∂μ)‖ ≤
      (Real.exp (-(BernoulliCLT.coefficient u).re * K) *
        (3 * ‖BernoulliCLT.coefficient u‖^2)) *
      ∫ ω, (X.probability k ω)^2 ∂μ := by
  rw [X.integral_compensation_drift]
  have hpint : Integrable (fun ω => (X.probability k ω)^2) μ := by
    simpa only [pow_two] using (X.integrable_probability k).mul_bdd
      ((X.predictable k).mono (X.filtration.le k)).aestronglyMeasurable
      (ae_of_all μ fun ω => by simpa [abs_of_nonneg (X.probability_nonneg k ω)]
        using X.probability_le_one k ω)
  calc
    _ ≤ ∫ ω, ‖X.characteristicCompensation u k ω *
      (Complex.exp (-BernoulliCLT.coefficient u * X.probability k ω) *
        (1 + BernoulliCLT.coefficient u * X.probability k ω) - 1)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (Real.exp (-(BernoulliCLT.coefficient u).re * K) *
        (3 * ‖BernoulliCLT.coefficient u‖^2)) * (X.probability k ω)^2 ∂μ := by
      apply integral_mono (X.compensation_drift_integrable u k).norm (hpint.const_mul _)
      intro ω
      have hpn : ‖BernoulliCLT.coefficient u * (X.probability k ω : ℂ)‖ =
          ‖BernoulliCLT.coefficient u‖ * X.probability k ω := by
        simp [abs_of_nonneg (X.probability_nonneg k ω)]
      have he := BernoulliCLT.exp_compensation_error
        (z := BernoulliCLT.coefficient u * X.probability k ω)
        (by rw [hpn]; exact (mul_le_of_le_one_right (norm_nonneg _)
          (X.probability_le_one k ω)).trans ha)
      rw [hpn] at he
      dsimp only
      rw [norm_mul]
      calc
        _ ≤ Real.exp (-(BernoulliCLT.coefficient u).re * K) *
            (3 * (‖BernoulliCLT.coefficient u‖ * X.probability k ω)^2) := by
          apply mul_le_mul (X.characteristicCompensation_bound u hK hk.le ω)
            (by simpa only [neg_mul] using he) (norm_nonneg _) (Real.exp_pos _).le
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

theorem characteristicCompensation_error {u K : ℝ} {N : ℕ}
    (ha : ‖BernoulliCLT.coefficient u‖ ≤ 1)
    (hK : ∀ ω, X.cltMass N ω ≤ K) :
    ‖(∫ ω, X.characteristicCompensation u N ω ∂μ) - 1‖ ≤
      (Real.exp (-(BernoulliCLT.coefficient u).re * K) *
        (3 * ‖BernoulliCLT.coefficient u‖^2)) * ∫ ω, X.cltSquares N ω ∂μ := by
  have h (m : ℕ) (hm : m ≤ N) :
      ‖(∫ ω, X.characteristicCompensation u m ω ∂μ) - 1‖ ≤
        ∑ k ∈ Finset.range m, (Real.exp (-(BernoulliCLT.coefficient u).re * K) *
          (3 * ‖BernoulliCLT.coefficient u‖^2)) * ∫ ω, (X.probability k ω)^2 ∂μ := by
    induction m with
    | zero => simp [characteristicCompensation, cltCount, cltMass]
    | succ m ih =>
      have hi := ih (Nat.le_of_succ_le hm)
      have hs := X.characteristicCompensation_step_error ha hK (Nat.lt_of_succ_le hm)
      rw [Finset.sum_range_succ]
      exact (norm_sub_le_norm_sub_add_norm_sub _
        (∫ ω, X.characteristicCompensation u m ω ∂μ) _).trans (by linarith)
  have he : (∫ ω, X.cltSquares N ω ∂μ) =
      ∑ k ∈ Finset.range N, ∫ ω, (X.probability k ω)^2 ∂μ := by
    apply integral_finsetSum
    intro k _
    simpa only [pow_two] using (X.integrable_probability k).mul_bdd
      ((X.predictable k).mono (X.filtration.le k)).aestronglyMeasurable
      (ae_of_all μ fun ω => by simpa [abs_of_nonneg (X.probability_nonneg k ω)]
        using X.probability_le_one k ω)
  simpa only [he, Finset.mul_sum] using h N le_rfl

end Luce.BernoulliProcess
