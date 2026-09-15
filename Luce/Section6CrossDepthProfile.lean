import Luce.Section6CrossDepthUniform
import Luce.Section6LeftHazard
import Luce.Section6RightHazard

noncomputable section
namespace Luce.Section6

/-- Off-diagonal right-corner time and hazard asymptotics, derived from
the exact sampled profile for either supported grid. -/
theorem PowerProfile.right_cross_depth_relative_error {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (grid : SamplingGrid) (w : WeightArray) (hw : SampledRates grid w f) :
    ∃ rho C delta M : ℝ, 0 < rho ∧ 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧ 1 ≤ M ∧
      ∀ n (i j : Fin n), M ≤ (terminalDepth i : ℝ) → M ≤ (terminalDepth j : ℝ) →
        (terminalDepth i : ℝ)/(n : ℝ) < delta → (terminalDepth j : ℝ)/(n : ℝ) < delta →
        let x := ((terminalDepth i : ℝ)/(terminalDepth j : ℝ))^beta
        let q := (Real.Gamma (1+1/beta))^beta
        let t := rightQuantileTime (w n) (terminalDepth j)
        let e := crossDepthError rho n (terminalDepth i) (terminalDepth j)
        |(w n).rate i*t/(q*x)-1| ≤ C*e ∧
        |((w n).rate i/((n : ℝ)*populationD (w n) 1 t))/(beta*q*x/(terminalDepth j : ℝ))-1| ≤ C*e := by
  obtain ⟨R, dr, hR, hdr, _, hr⟩ := hp.right_sampled_rate_relative_error
  obtain ⟨T, dt, Mt, hT, hdt, _, ht⟩ := hp.right_rate_time_relative_error
  obtain ⟨H, dh, Mh, hH, hdh, _, hh⟩ := hp.right_quantile_hazard_relative_error
  have hb := hp.2.2.2.1.2.1
  have he := hp.2.2.2.1.2.2.1
  have hq : 0 < (Real.Gamma (1+1/beta))^beta :=
    Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (by positivity)) _
  exact cross_depth_uniform_transport
    (fun _ i => terminalDepth i) (fun n => (w n).rate)
    (fun n i => rightQuantileTime (w n) (terminalDepth i))
    (fun n i => (n : ℝ)*populationD (w n) 1 (rightQuantileTime (w n) (terminalDepth i)))
    (fun _ i => terminalDepth_pos i) (fun n i => (w n).positive i)
    hp.2.2.2.1.1 hb hq he he he hR hT hH hdr hdt hdh
    (hr grid w hw) (ht grid w hw) (hh grid w hw)

/-- Off-diagonal left-corner time and hazard asymptotics. Unbounded
sampled rates are retained; no bound on the rates is introduced. -/
theorem PowerProfile.left_cross_depth_relative_error {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (grid : SamplingGrid) (w : WeightArray) (hw : SampledRates grid w f) :
    ∃ rho C delta M : ℝ, 0 < rho ∧ 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧ 1 ≤ M ∧
      ∀ n (i j : Fin n), M ≤ ((i.val : ℝ)+1) → M ≤ ((j.val : ℝ)+1) →
        ((i.val : ℝ)+1)/(n : ℝ) < delta → ((j.val : ℝ)+1)/(n : ℝ) < delta →
        let x := (((j.val : ℝ)+1)/((i.val : ℝ)+1))^alpha
        let q := (Real.Gamma (1-1/alpha))^(-alpha)
        let t := leftQuantileTime (w n) (j.val+1)
        let e := crossDepthError rho n ((i.val : ℝ)+1) ((j.val : ℝ)+1)
        |(w n).rate i*t/(q*x)-1| ≤ C*e ∧
        |((w n).rate i/((n : ℝ)*populationD (w n) 1 t))/(alpha*q*x/((j.val : ℝ)+1))-1| ≤ C*e := by
  obtain ⟨R, dr, hR, hdr, _, hr⟩ := hp.left_sampled_rate_relative_error
  obtain ⟨xr, T, dt, Mt, hxr, hT, hdt, _, ht⟩ := hp.left_rate_time_relative_error
  obtain ⟨xh, H, dh, Mh, hxh, hH, hdh, _, hh⟩ := hp.left_quantile_hazard_relative_error
  have ha := hp.2.2.1.2.1
  have ha0 := zero_lt_one.trans ha
  have he := hp.2.2.1.2.2.1
  have hG : 0 < Real.Gamma (1-1/alpha) := by
    apply Real.Gamma_pos_of_pos
    have hi := one_div_lt_one_div_of_lt zero_lt_one ha
    rw [div_one] at hi
    linarith
  have hq : 0 < (Real.Gamma (1-1/alpha))^(-alpha) := Real.rpow_pos_of_pos hG _
  obtain ⟨rho, C, delta, M, hrho, hC, hd, hd1, hM, hcross⟩ := cross_depth_uniform_transport
    (fun _ i => i.val+1) (fun n => (w n).rate)
    (fun n i => leftQuantileTime (w n) (i.val+1))
    (fun n i => (n : ℝ)*populationD (w n) 1 (leftQuantileTime (w n) (i.val+1)))
    (fun _ _ => Nat.succ_pos _) (fun n i => (w n).positive i)
    hp.2.2.1.1 ha0 hq he hxr hxh hR hT hH hdr hdt hdh
    (by simpa only [Nat.cast_add, Nat.cast_one] using hr grid w hw)
    (by simpa only [Nat.cast_add, Nat.cast_one] using ht grid w hw)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hh grid w hw)
  refine ⟨rho, C, delta, M, hrho, hC, hd, hd1, hM, ?_⟩
  intro n i j hi hj his hjs
  have hc := hcross n i j (by simpa using hi) (by simpa using hj)
    (by simpa using his) (by simpa using hjs)
  dsimp only at hc ⊢
  simpa only [Nat.cast_add, Nat.cast_one,
    left_power_ratio (by positivity : 0 < (i.val : ℝ)+1) (by positivity : 0 < (j.val : ℝ)+1)] using hc

end Luce.Section6
