import Luce.Section6PopulationPowerBounds
import Luce.Section6ExcursionDepthSums

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- A weaker, summable replacement for logarithmic-bin counting in the
critical-pole cycle estimate. Constants are uniform in both z and R. -/
theorem critical_range_decay {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ z R : ℝ, 1 ≤ z → 0 ≤ R →
      Real.exp (-c*(Real.exp (R/d)/(z+R))) ≤
        C*z^(1/2 : ℝ)*Real.exp (-R/(4*d)) := by
  obtain ⟨E,hE,he⟩ := exponential_le_power (a := (1/2 : ℝ)) (by norm_num) hc
  refine ⟨E*(1+2*d)^(1/2 : ℝ), by positivity, ?_⟩
  intro z R hz hR
  have hz0 : 0 < z := by linarith
  have hzR : 0 < z+R := by positivity
  have heR : 0 < Real.exp (R/d) := Real.exp_pos _
  have hbound := he (Real.exp (R/d)/(z+R)) (div_pos heR hzR)
  have hid : (Real.exp (R/d)/(z+R))^(-(1/2 : ℝ)) =
      (z+R)^(1/2 : ℝ)*Real.exp (-R/(2*d)) := by
    rw [Real.div_rpow heR.le hzR.le, ← Real.exp_mul,
      Real.rpow_neg hzR.le, div_inv_eq_mul]
    rw [mul_comm]
    congr 1
    congr 1
    ring
  rw [hid] at hbound
  rw [← neg_mul] at hbound
  have hsum : 1+R ≤ (1+2*d)*Real.exp (R/(2*d)) := by
    have h1 := Real.add_one_le_exp (R/(2*d))
    have h2 : 1 ≤ Real.exp (R/(2*d)) := Real.one_le_exp_iff.mpr (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2*d)
    have heq : (2*d)*(R/(2*d)+1) = R+2*d := by field_simp <;> ring
    rw [heq] at h3
    nlinarith only [h2,h3,hd]
  have hprod : z+R ≤ z*(1+R) := by nlinarith only [hz,hR]
  have hpow : (z+R)^(1/2 : ℝ) ≤
      z^(1/2 : ℝ)*(1+2*d)^(1/2 : ℝ)*Real.exp (R/(4*d)) := by
    calc
      _ ≤ (z*(1+R))^(1/2 : ℝ) := Real.rpow_le_rpow hzR.le hprod (by norm_num)
      _ = z^(1/2 : ℝ)*(1+R)^(1/2 : ℝ) := Real.mul_rpow hz0.le (by positivity)
      _ ≤ z^(1/2 : ℝ)*((1+2*d)*Real.exp (R/(2*d)))^(1/2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hsum (by norm_num)) (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
        have heq : R/(2*d)*(1/2 : ℝ) = R/(4*d) := by ring
        rw [heq]
        ring
  calc
    _ ≤ E*((z+R)^(1/2 : ℝ)*Real.exp (-R/(2*d))) := hbound
    _ ≤ E*((z^(1/2 : ℝ)*(1+2*d)^(1/2 : ℝ)*Real.exp (R/(4*d)))*Real.exp (-R/(2*d))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le) hE.le
    _ = (E*(1+2*d)^(1/2 : ℝ))*z^(1/2 : ℝ)*Real.exp (-R/(4*d)) := by
      have heq : Real.exp (R/(4*d))*Real.exp (-R/(2*d)) = Real.exp (-R/(4*d)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = E*z^(1/2 : ℝ)*(1+2*d)^(1/2 : ℝ)*
          (Real.exp (R/(4*d))*Real.exp (-R/(2*d))) := by ring
        _ = (E*(1+2*d)^(1/2 : ℝ))*z^(1/2 : ℝ)*Real.exp (-R/(4*d)) := by rw [heq] <;> ring

/-- Distributing range decay reduces every remaining vertex to an
already established weighted harmonic sum. -/
theorem critical_weighted_vertex_sum {a : ℝ} (ha : 0 < a) {M m : ℕ}
    (hM : 1 ≤ M) (hMm : M ≤ m) :
    ∑ i ∈ Finset.Icc M m, (1/(i : ℝ))*((i : ℝ)/(m : ℝ))^a ≤ 1+1/a :=
  right_excursion_kernel_sum ha hM hMm

end Luce.Section6
