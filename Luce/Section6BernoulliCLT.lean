import Luce.Section6BernoulliCLTCapped
import Luce.Section6BernoulliCLTStopping
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

/-! The adapted Bernoulli central limit criterion on varying row spaces.
The proof uses predictable deletion and compensated characteristic functions. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction

namespace Luce.BernoulliCLT

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
  (X : ∀ n, BernoulliProcess (μ n)) (N : ℕ → ℕ) {v : ℕ → ℝ}

theorem characteristic_tendsto_of_one_le (hv : ∀ n, 1 ≤ v n) (hvlim : Tendsto v atTop atTop)
    (hA : ConvergesInProbability μ
      (fun n ω => ((X n).cltMass (N n) ω-v n)/Real.sqrt (v n)) 0)
    (hB : ConvergesInProbability μ (fun n ω => (X n).cltSquares (N n) ω/v n) 0)
    (t : ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp
      (((((X n).cltCount (N n) ω-v n)/Real.sqrt (v n))*t : ℝ) * Complex.I) ∂μ n)
      atTop (𝓝 (Complex.exp (-(t : ℂ)^2/2))) := by
  let Y (n : ℕ) := (X n).stop 1 (2*v n)
  let bad (n : ℕ) := {ω | 2*v n < (X n).cltMass (N n) ω}
  have hbad : Tendsto (fun n => (μ n).real (bad n)) atTop (𝓝 0) :=
    mass_cap_probability μ hv hA
  have hv0 (n : ℕ) : 0 < v n := lt_of_lt_of_le zero_lt_one (hv n)
  have heq (n : ℕ) (ω : Ω n) (hω : ω ∉ bad n) :
      (Y n).cltCount (N n) ω = (X n).cltCount (N n) ω ∧
      (Y n).cltMass (N n) ω = (X n).cltMass (N n) ω :=
    (X n).stop_clt_eq_of_mass_le (le_of_not_gt hω)
  have hYA : ConvergesInProbability μ
      (fun n ω => ((Y n).cltMass (N n) ω-v n)/Real.sqrt (v n)) 0 :=
    hA.congr_off bad hbad (fun n ω hω => by rw [(heq n ω hω).2])
  have hYB : ConvergesInProbability μ
      (fun n ω => (Y n).cltSquares (N n) ω/v n) 0 := by
    apply hB.mono
    intro n ω
    simp only [sub_zero, abs_of_nonneg (div_nonneg
      (BernoulliProcess.cltSquares_nonneg _ _ _) (hv0 n).le)]
    exact div_le_div_of_nonneg_right ((X n).stop_cltSquares_le _ _ _) (hv0 n).le
  have hc := capped_characteristic_tendsto μ Y N hv hvlim
    (fun n ω => (X n).stop_cltMass_le _ (mul_nonneg (by norm_num) (hv0 n).le) _ ω) hYA hYB t
  let F (n : ℕ) (ω : Ω n) := Complex.exp
    (((((X n).cltCount (N n) ω-v n)/Real.sqrt (v n))*t : ℝ) * Complex.I)
  let G (n : ℕ) (ω : Ω n) := Complex.exp
    (((((Y n).cltCount (N n) ω-v n)/Real.sqrt (v n))*t : ℝ) * Complex.I)
  have hfmeas (n : ℕ) : Measurable (F n) := by
    have hm := (X n).cltCount_measurable (N n)
    dsimp [F]
    fun_prop
  have hgmeas (n : ℕ) : Measurable (G n) := by
    have hm := (Y n).cltCount_measurable (N n)
    dsimp [G]
    fun_prop
  have hFn (n : ℕ) (ω : Ω n) : ‖F n ω‖ ≤ 1 := by simp [F, Complex.norm_exp]
  have hGn (n : ℕ) (ω : Ω n) : ‖G n ω‖ ≤ 1 := by simp [G, Complex.norm_exp]
  have hd : Tendsto (fun n => (∫ ω, F n ω ∂μ n)-(∫ ω, G n ω ∂μ n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using hbad.const_mul 2)
    intro n
    apply integral_complex_difference_off
      ((integrable_const (1:ℝ)).mono' (hfmeas n).aestronglyMeasurable (ae_of_all _ (hFn n)))
      ((integrable_const (1:ℝ)).mono' (hgmeas n).aestronglyMeasurable (ae_of_all _ (hGn n)))
      (hFn n) (hGn n) (bad n)
      (measurableSet_lt measurable_const ((X n).cltMass_measurable (N n)))
    intro ω hω
    dsimp [F,G]
    rw [(heq n ω hω).1]
  simpa only [F, G, sub_add_cancel, zero_add] using hd.add hc

theorem characteristic_tendsto (hvlim : Tendsto v atTop atTop)
    (hA : ConvergesInProbability μ
      (fun n ω => ((X n).cltMass (N n) ω-v n)/Real.sqrt (v n)) 0)
    (hB : ConvergesInProbability μ (fun n ω => (X n).cltSquares (N n) ω/v n) 0)
    (t : ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp
      (((((X n).cltCount (N n) ω-v n)/Real.sqrt (v n))*t : ℝ) * Complex.I) ∂μ n)
      atTop (𝓝 (Complex.exp (-(t : ℂ)^2/2))) := by
  let w (n : ℕ) := max 1 (v n)
  have he : w =ᶠ[atTop] v := by
    filter_upwards [hvlim.eventually_ge_atTop 1] with n hn
    exact max_eq_right hn
  have hwlim : Tendsto w atTop atTop := hvlim.congr' he.symm
  have hAw : ConvergesInProbability μ
      (fun n ω => ((X n).cltMass (N n) ω-w n)/Real.sqrt (w n)) 0 := by
    intro ε hε
    apply (hA ε hε).congr'
    filter_upwards [he] with n hn
    simp only [hn]
  have hBw : ConvergesInProbability μ (fun n ω => (X n).cltSquares (N n) ω/w n) 0 := by
    intro ε hε
    apply (hB ε hε).congr'
    filter_upwards [he] with n hn
    simp only [hn]
  apply (characteristic_tendsto_of_one_le μ X N (v := w)
    (fun n => le_max_left _ _) hwlim hAw hBw t).congr'
  filter_upwards [he] with n hn
  simp only [hn]

/-- The full distributional conclusion, tested against every bounded continuous function. -/
theorem boundedContinuous_tendsto (hvlim : Tendsto v atTop atTop)
    (hA : ConvergesInProbability μ
      (fun n ω => ((X n).cltMass (N n) ω-v n)/Real.sqrt (v n)) 0)
    (hB : ConvergesInProbability μ (fun n ω => (X n).cltSquares (N n) ω/v n) 0)
    (F : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω,
      F (((X n).cltCount (N n) ω-v n)/Real.sqrt (v n)) ∂μ n)
      atTop (𝓝 (∫ x, F x ∂ProbabilityTheory.gaussianReal 0 1)) := by
  let Y (n : ℕ) (ω : Ω n) := ((X n).cltCount (N n) ω-v n)/Real.sqrt (v n)
  have hm (n : ℕ) : Measurable (Y n) := ((X n).cltCount_measurable (N n)).sub_const _ |>.div_const _
  let laws (n : ℕ) : ProbabilityMeasure ℝ :=
    ⟨(μ n).map (Y n), Measure.isProbabilityMeasure_map (hm n).aemeasurable⟩
  let normal : ProbabilityMeasure ℝ := ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩
  have hlaw : Tendsto laws atTop (𝓝 normal) := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro t
    have he (n : ℕ) : charFun (laws n : Measure ℝ) t =
        ∫ ω, Complex.exp (((Y n ω)*t : ℝ)*Complex.I) ∂μ n := by
      change charFun ((μ n).map (Y n)) t = _
      rw [charFun_apply_real, integral_map (hm n).aemeasurable (by fun_prop)]
      apply integral_congr_ae
      apply ae_of_all
      intro ω
      change Complex.exp ((t : ℂ)*(Y n ω : ℂ)*Complex.I) =
        Complex.exp (((Y n ω*t : ℝ) : ℂ)*Complex.I)
      congr 1
      push_cast
      ring
    simp_rw [he]
    change Tendsto _ atTop (𝓝 (charFun (ProbabilityTheory.gaussianReal 0 1) t))
    simpa [ProbabilityTheory.charFun_gaussianReal, Y, neg_div] using
      characteristic_tendsto μ X N hvlim hA hB t
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlaw F
  have he (n : ℕ) : (∫ x, F x ∂(laws n : Measure ℝ)) = ∫ ω, F (Y n ω) ∂μ n :=
    integral_map (hm n).aemeasurable F.continuous.measurable.aestronglyMeasurable
  simp_rw [he] at h
  exact h

end Luce.BernoulliCLT
