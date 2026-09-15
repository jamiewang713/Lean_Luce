import Luce.Section6IdealCoreGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter
open scoped Topology
namespace Luce.Section6

theorem core_error_tendsto65 (K : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => (1+Real.log (n : ℝ))^K *
      (idealCoreLower n : ℝ)^(-κ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp hlog
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4*K) κ hκ).comp ht
  have hlim' := hlim.const_mul ((2 : ℝ)^K)
  simp only [mul_zero] at hlim'
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) ?_ hlim'
  filter_upwards [hlog.eventually_ge_atTop 1] with n hn
  let l := Real.log (n : ℝ)
  let t := l^(1/4 : ℝ)
  have hl : 0 < l := lt_of_lt_of_le (by norm_num) hn
  have hA : Real.exp t ≤ (idealCoreLower n : ℝ) := Nat.le_ceil _
  have he : (idealCoreLower n : ℝ)^(-κ) ≤ Real.exp (-κ*t) := by
    calc
      _ ≤ (Real.exp t)^(-κ) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hA (by linarith)
      _ = _ := by rw [← Real.exp_mul]; congr 1; ring
  have hp : (1+l)^K ≤ (2 : ℝ)^K * l^K := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by dsimp [l]; linarith) K
  have heq : t^(4*(K : ℝ)) = l^K := by
    dsimp [t]
    rw [← Real.rpow_mul hl.le]
    convert Real.rpow_natCast l K using 1 <;> ring
  change (1+l)^K * (idealCoreLower n : ℝ)^(-κ) ≤
    (2 : ℝ)^K * (t^(4*(K : ℝ)) * Real.exp (-κ*t))
  rw [heq, ← mul_assoc]
  exact mul_le_mul hp he (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)

end Luce.Section6
