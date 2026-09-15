import Luce.Section6BernoulliReferenceApproximation

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Luce.BernoulliCLT

theorem mean_tendsto_of_reference
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, BernoulliProcess (μ n)) (N : ℕ → ℕ) (q : ℕ → ℕ → ℝ) {v : ℕ → ℝ}
    (hv : Tendsto v atTop atTop) {C : ℝ} (herr : ∀ᶠ n in atTop,
      (∑ k ∈ Finset.range (N n), ∫ ω, |(X n).probability k ω-q n k| ∂μ n) ≤ C ∧
      |(∑ k ∈ Finset.range (N n), q n k)-v n| ≤ C) :
    Tendsto (fun n => (∫ ω, (X n).cltCount (N n) ω ∂μ n)/v n) atTop (𝓝 1) := by
  have hb : ∀ᶠ n in atTop,
      |(∫ ω, (X n).cltCount (N n) ω ∂μ n)-v n| ≤ 2*C := by
    filter_upwards [herr] with n hn
    have hi : Integrable ((X n).cltMass (N n)) (μ n) :=
      integrable_finsetSum _ fun k _ => (X n).integrable_probability k
    have he : (∫ ω, (X n).cltCount (N n) ω ∂μ n) = ∫ ω, (X n).cltMass (N n) ω ∂μ n :=
      (X n).integral_sum_observation (N n)
    have hc : (∫ ω, (X n).cltMass (N n) ω-v n ∂μ n) =
        (∫ ω, (X n).cltMass (N n) ω ∂μ n)-v n := by
      rw [integral_sub hi (integrable_const _),integral_const]
      simp
    rw [he,← hc]
    exact abs_integral_le_integral_abs.trans
      (((X n).reference_mass_error (N n) (q n) (v n)).trans (by linarith [hn.1,hn.2]))
  have hzero : Tendsto (fun n => ((∫ ω, (X n).cltCount (N n) ω ∂μ n)-v n)/v n)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun n => (2*C)/v n) atTop (𝓝 0) from
      tendsto_const_nhds.div_atTop hv)
    filter_upwards [hb,hv.eventually_gt_atTop 0] with n hn hvn
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hvn]
    exact div_le_div_of_nonneg_right hn hvn.le
  have hh := hzero.add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [hv.eventually_gt_atTop 0] with n hn
  field_simp
  ring

end Luce.BernoulliCLT
