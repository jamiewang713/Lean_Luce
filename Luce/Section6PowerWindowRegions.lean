import Luce.Section6Sampling

noncomputable section
namespace Luce.Section6

/-- Every time in a fixed multiplicative window about the right leading
scale lies in the population region, after choosing joint-regime cutoffs. -/
theorem negative_power_window_region {A p S M : ℝ}
    (hA : 0 < A) (hp : 0 < p) (hS : 0 < S) (hM : 0 < M) :
    ∃ delta B : ℝ, 0 < delta ∧ 0 < B ∧
    ∀ N m : ℝ, 0 < N → 0 < m → B ≤ m → m/N < delta →
      let T := (A/(m/N))^(1/p)
      ∀ s : ℝ, T/16 ≤ s → s ≤ 16*T → S ≤ s ∧ M ≤ N*s^(-p) := by
  have hSp : 0 < (16*S)^p := Real.rpow_pos_of_pos (by positivity) _
  have h16 : 0 < (16 : ℝ)^p := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨A/(16*S)^p, M*A*(16 : ℝ)^p, div_pos hA hSp, by positivity, ?_⟩
  intro N m hN hm hlarge hsmall
  let x := m/N
  let T := (A/x)^(1/p)
  have hx : 0 < x := div_pos hm hN
  have hT : 0 < T := Real.rpow_pos_of_pos (div_pos hA hx) _
  have hTpow : T^(-p) = x/A := by
    dsimp [T]
    rw [← Real.rpow_mul (div_pos hA hx).le,
      show (1/p)*(-p) = (-1 : ℝ) by field_simp, Real.rpow_neg_one]
    field_simp
  have hbigT : 16*S < T := by
    have hbase : (16*S)^p < A/x := by
      apply (lt_div_iff₀ hx).mpr
      have hh := (lt_div_iff₀ hSp).mp hsmall
      change x*(16*S)^p < A at hh
      nlinarith
    have hh := Real.rpow_lt_rpow hSp.le hbase (one_div_pos.mpr hp)
    rw [← Real.rpow_mul (by positivity : 0 ≤ 16*S),
      show p*(1/p) = (1 : ℝ) by field_simp, Real.rpow_one] at hh
    exact hh
  change ∀ s : ℝ, T/16 ≤ s → s ≤ 16*T → S ≤ s ∧ M ≤ N*s^(-p)
  intro s hslo hshi
  have hs0 : 0 < s := (div_pos hT (by norm_num)).trans_le hslo
  constructor
  · linarith
  · have hpbound := Real.rpow_le_rpow_of_nonpos hs0 hshi (by linarith : -p ≤ 0)
    have hid : N*(16*T)^(-p) = m/(A*(16 : ℝ)^p) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) hT.le, hTpow, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16)]
      dsimp [x]
      field_simp
    have hlow : M ≤ m/(A*(16 : ℝ)^p) := by
      apply (le_div_iff₀ (mul_pos hA h16)).mpr
      nlinarith
    exact hlow.trans (hid ▸ mul_le_mul_of_nonneg_left hpbound hN.le)

theorem positive_power_window_region {A p S M : ℝ}
    (hA : 0 < A) (hp : 0 < p) (hS : 0 < S) (hM : 0 < M) :
    ∃ delta B : ℝ, 0 < delta ∧ 0 < B ∧
    ∀ N m : ℝ, 0 < N → 0 < m → B ≤ m → m/N < delta →
      let T := ((m/N)/A)^(1/p)
      ∀ s : ℝ, T/16 ≤ s → s ≤ 16*T → s ≤ S ∧ M ≤ N*s^p := by
  have hSp : 0 < (S/16)^p := Real.rpow_pos_of_pos (by positivity) _
  have h16 : 0 < (16 : ℝ)^p := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨A*(S/16)^p, M*A*(16 : ℝ)^p, mul_pos hA hSp, by positivity, ?_⟩
  intro N m hN hm hlarge hsmall
  let x := m/N
  let T := (x/A)^(1/p)
  have hx : 0 < x := div_pos hm hN
  have hT : 0 < T := Real.rpow_pos_of_pos (div_pos hx hA) _
  have hTpow : T^p = x/A := by
    dsimp [T]
    rw [← Real.rpow_mul (div_pos hx hA).le,
      show (1/p)*p = (1 : ℝ) by field_simp, Real.rpow_one]
  have hsmallT : T < S/16 := by
    have hbase : x/A < (S/16)^p := by
      apply (div_lt_iff₀ hA).mpr
      change x < A*(S/16)^p at hsmall
      nlinarith
    have hh := Real.rpow_lt_rpow (div_pos hx hA).le hbase (one_div_pos.mpr hp)
    rw [← Real.rpow_mul (by positivity : 0 ≤ S/16),
      show p*(1/p) = (1 : ℝ) by field_simp, Real.rpow_one] at hh
    exact hh
  change ∀ s : ℝ, T/16 ≤ s → s ≤ 16*T → s ≤ S ∧ M ≤ N*s^p
  intro s hslo hshi
  constructor
  · linarith
  · have hpbound := Real.rpow_le_rpow (by positivity : 0 ≤ T/16) hslo hp.le
    have hid : N*(T/16)^p = m/(A*(16 : ℝ)^p) := by
      rw [Real.div_rpow hT.le (by norm_num : (0 : ℝ) ≤ 16), hTpow]
      dsimp [x]
      field_simp
    have hlow : M ≤ m/(A*(16 : ℝ)^p) := by
      apply (le_div_iff₀ (mul_pos hA h16)).mpr
      nlinarith
    exact hlow.trans (hid ▸ mul_le_mul_of_nonneg_left hpbound hN.le)

end Luce.Section6
