import Luce.Section6PowerInverseBounds

noncomputable section
open Set
namespace Luce.Section6

/-- Quantitative inversion of a positive-power population error. The
two smallness premises will be discharged at the actual finite quantile
using monotonicity and the same population estimate. -/
theorem positive_power_inverse_estimate {A p q K : ℝ}
    (hA : 0 < A) (hp : 0 < p) (hq : 0 < q) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ N x t : ℝ, 0 < N → 0 < x → 0 < t →
      |x-A*t^p| ≤ K*(t^(p+q)+1/N) →
      K*t^q ≤ A/4 → K/N ≤ x/4 →
      |t/(x/A)^(1/p)-1| ≤ C*(x^(q/p)+1/(N*x)) := by
  obtain ⟨L, hL, hlip⟩ := positive_power_relative_error hp
  let B := (2*K/A)*(2/A)^(q/p)
  have hB : 0 < B := mul_pos (div_pos (by positivity) hA)
    (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨L*(B+K), mul_pos hL (add_pos hB hK), ?_⟩
  intro N x t hN hx ht herr hsmall hdisc
  let y := A*t^p
  have hy : 0 < y := mul_pos hA (Real.rpow_pos_of_pos ht _)
  have hprod : t^(p+q) = t^p*t^q := by
    rw [← Real.rpow_add ht]
  have herr' : |x-y| ≤ y/4+x/4 := by
    have hs := mul_le_mul_of_nonneg_left hsmall (Real.rpow_pos_of_pos ht p).le
    rw [hprod] at herr
    calc
      _ ≤ K*(t^p*t^q+1/N) := herr
      _ = t^p*(K*t^q)+K/N := by ring
      _ ≤ t^p*(A/4)+x/4 := add_le_add hs hdisc
      _ = _ := by dsimp [y]; ring
  have hratio : y/x ∈ Icc (1/2 : ℝ) 2 := by
    have hh := abs_le.mp herr'
    constructor
    · apply (le_div_iff₀ hx).mpr
      linarith [hh.1, hh.2]
    · apply (div_le_iff₀ hx).mpr
      linarith [hh.1, hh.2]
  have htbase : t^p ≤ 2*x/A := by
    have hh := (div_le_iff₀ hx).mp hratio.2
    apply (le_div_iff₀ hA).mpr
    dsimp [y] at hh
    nlinarith
  have htq : t^q ≤ (2/A)^(q/p)*x^(q/p) := by
    have hh := Real.rpow_le_rpow (Real.rpow_pos_of_pos ht p).le htbase (div_pos hq hp).le
    rw [← Real.rpow_mul ht.le, show p*(q/p) = q by field_simp] at hh
    rw [show 2*x/A = (2/A)*x by ring, Real.mul_rpow (by positivity) hx.le] at hh
    exact hh
  have hscale : (t/(x/A)^(1/p))^p = y/x := by
    have hT := Real.rpow_pos_of_pos (div_pos hx hA) (1/p)
    rw [Real.div_rpow ht.le hT.le, ← Real.rpow_mul (div_pos hx hA).le,
      show (1/p)*p = (1 : ℝ) by field_simp, Real.rpow_one]
    dsimp [y]
    field_simp
  have hpower : |y/x-1| ≤ B*x^(q/p)+K/(N*x) := by
    have he : |y/x-1| ≤ K*(t^(p+q)+1/N)/x := by
      rw [div_sub_one hx.ne', abs_div, abs_of_pos hx, abs_sub_comm]
      exact div_le_div_of_nonneg_right herr hx.le
    have hmul := mul_le_mul hratio.2 htq (Real.rpow_pos_of_pos ht q).le (by norm_num)
    have hmul' := mul_le_mul_of_nonneg_left hmul (div_pos hK hA).le
    have hid : K*(t^(p+q)+1/N)/x =
        (K/A)*((y/x)*t^q)+K/(N*x) := by
      rw [hprod]
      dsimp [y]
      field_simp
    rw [hid] at he
    exact he.trans ((add_le_add hmul' (le_refl (K/(N*x)))).trans_eq (by dsimp [B]; ring))
  have hi := hlip t ((x/A)^(1/p)) ht (Real.rpow_pos_of_pos (div_pos hx hA) _)
    (by simpa only [hscale] using hratio)
  rw [hscale] at hi
  have hp0 := (Real.rpow_pos_of_pos hx (q/p)).le
  have hd0 : 0 ≤ 1/(N*x) := by positivity
  calc
    _ ≤ L*(B*x^(q/p)+K/(N*x)) := hi.trans (mul_le_mul_of_nonneg_left hpower hL.le)
    _ ≤ _ := by
      have h1 := mul_nonneg hB.le hd0
      have h2 := mul_nonneg hK.le hp0
      have hsum : B*x^(q/p)+K/(N*x) ≤ (B+K)*(x^(q/p)+1/(N*x)) := by
        rw [div_eq_mul_one_div K]
        nlinarith
      exact (mul_le_mul_of_nonneg_left hsum hL.le).trans_eq (by ring)

end Luce.Section6
