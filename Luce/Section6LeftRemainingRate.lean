import Luce.Section6LeftRateFloor
import Luce.Section6InitialBlockSurvivors

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- The left remaining-rate floor, uniformly over every removal set with
at most twice the reference rank. This includes bounded deletions and
bounded rank displacements once their elementary cardinality bound holds. -/
theorem PowerProfile.left_remaining_rate_floor {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ C eps : ℝ, 0 < C ∧ 0 < eps ∧ eps < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → 0 < h → (3*(h : ℝ))/(n : ℝ) < eps →
    ∀ removed : Finset (Fin n), removed.card ≤ 2*h →
      C*(n : ℝ)^alpha*(h : ℝ)^(1-alpha) ≤
        ∑ i ∈ Finset.univ \ removed, (w n).rate i := by
  have hc := hp.2.2.1.1
  obtain ⟨eps, heps, heps1, hblock⟩ := hp.left_initial_block_rate_floor
  refine ⟨(c/2)*(3 : ℝ)^(-alpha), eps,
    mul_pos (half_pos hc) (Real.rpow_pos_of_pos (by norm_num) _), heps, heps1, ?_⟩
  intro grid w hw n h hn hh hsmall removed hremoved
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hkn : 3*h ≤ n := by
    have hh' := (div_lt_one hnR).mp (hsmall.trans heps1)
    exact_mod_cast hh'.le
  have hsmall' : ((3*h : ℕ) : ℝ)/(n : ℝ) < eps := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsmall
  have hb := initial_block_remaining_rate (w n) hkn removed
    (show removed.card+h ≤ 3*h by omega)
    (mul_nonneg (half_pos hc).le (Real.rpow_nonneg (by positivity) _))
    (hblock grid w hw n (3*h) hn hsmall')
  have hid : (h : ℝ)*((c/2)*(((3*h : ℕ) : ℝ)/(n : ℝ))^(-alpha)) =
      ((c/2)*(3 : ℝ)^(-alpha))*(n : ℝ)^alpha*(h : ℝ)^(1-alpha) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.div_rpow (by positivity) hnR.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hhR.le,
      Real.rpow_neg hnR.le, div_inv_eq_mul]
    rw [show (1-alpha : ℝ) = 1+(-alpha) by ring,
      Real.rpow_add hhR, Real.rpow_one]
    ring
  exact hid ▸ hb

/-- A bounded total deletion/displacement budget, in the rank range used
by the manuscript. The budget bounds the cardinality of actual removals;
it is not a new hypothesis on the rate family. -/
theorem PowerProfile.left_remaining_rate_floor_bounded_displacement {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ C eps : ℝ, 0 < C ∧ 0 < eps ∧ eps < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h r : ℕ, 0 < n → 4*r+4 ≤ h → (h : ℝ) ≤ eps*(n : ℝ)/4 →
    ∀ removed : Finset (Fin n), removed.card ≤ h+r →
      C*(n : ℝ)^alpha*(h : ℝ)^(1-alpha) ≤
        ∑ i ∈ Finset.univ \ removed, (w n).rate i := by
  obtain ⟨C, eps, hC, heps, heps1, hfloor⟩ := hp.left_remaining_rate_floor
  refine ⟨C, eps, hC, heps, heps1, ?_⟩
  intro grid w hw n h r hn hr hh removed hremoved
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply hfloor grid w hw n h hn (by omega) _ removed (by omega)
  apply (div_lt_iff₀ hnR).mpr
  nlinarith [mul_pos heps hnR]

end Luce.Section6
