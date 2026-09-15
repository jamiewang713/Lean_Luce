import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace Luce.Section6

theorem factorial_error_algebra {A b kappa eta C0 CM p q Q H J : ℝ}
    (hA : 1 ≤ A) (hb : 0 ≤ b) (hbA : b ≤ 1/A) (hk : 0 < kappa)
    (he1 : eta ≤ 1) (hek : eta ≤ kappa)
    (h0 : 0 ≤ C0) (hm : 0 ≤ CM) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hQ : 1 ≤ Q) (hH : 1 ≤ H) (hHJ : H ≤ J) (s : ℕ) :
    C0*(A^(-kappa)+b^kappa)*(Q*H)^s +
      (CM+1)*(p/A*(Q*H)^(s-1)+q*((Q*H)/A^eta)*(Q*H)^(s-1)) ≤
      (2*C0+(CM+1)*(p+q))*Q^(s+1)*J^(s+1)*A^(-eta) := by
  have ha : 0 < A := zero_lt_one.trans_le hA
  have hAeta : 0 ≤ A^(-eta) := Real.rpow_nonneg ha.le _
  have hAk : A^(-kappa) ≤ A^(-eta) := Real.rpow_le_rpow_of_exponent_le hA (by linarith)
  have hbk : b^kappa ≤ A^(-eta) := by
    apply (Real.rpow_le_rpow hb hbA hk.le).trans
    have he : (1/A)^kappa = A^(-kappa) := by
      rw [one_div, Real.inv_rpow ha.le, Real.rpow_neg ha.le]
    rw [he]
    exact hAk
  have hInv : 1/A ≤ A^(-eta) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hA (by linarith)
  have hInvEta : 1/A^eta = A^(-eta) := by rw [Real.rpow_neg ha.le, one_div]
  let T := Q*H
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hQ hH
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hs : T^s ≤ T^(s+1) := pow_le_pow_right₀ hT (Nat.le_succ s)
  have hs' : T^(s-1) ≤ T^(s+1) := pow_le_pow_right₀ hT (by omega)
  have hts : T*T^(s-1) ≤ T^(s+1) := by
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega : s-1 ≤ s)) hT0
  have hlocal : C0*(A^(-kappa)+b^kappa)*T^s ≤ 2*C0*(T^(s+1)*A^(-eta)) := by
    have hsum : A^(-kappa)+b^kappa ≤ 2*A^(-eta) := by linarith
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul hsum hs (pow_nonneg hT0 s) (mul_nonneg (by norm_num) hAeta)) h0
    calc
      _ = C0*((A^(-kappa)+b^kappa)*T^s) := by ring
      _ ≤ C0*((2*A^(-eta))*T^(s+1)) := hh
      _ = _ := by ring
  have hcol : p/A*T^(s-1) ≤ p*(T^(s+1)*A^(-eta)) := by
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul hInv hs' (pow_nonneg hT0 _) hAeta) hp
    calc
      _ = p*((1/A)*T^(s-1)) := by ring
      _ ≤ p*(A^(-eta)*T^(s+1)) := hh
      _ = _ := by ring
  have hmod : q*(T/A^eta)*T^(s-1) ≤ q*(T^(s+1)*A^(-eta)) := by
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hts hAeta) hq
    rw [← hInvEta] at hh
    calc
      _ = q*((T*T^(s-1))*(1/A^eta)) := by ring
      _ ≤ q*(T^(s+1)*(1/A^eta)) := hh
      _ = _ := by rw [hInvEta]
  have hconst : 0 ≤ 2*C0+(CM+1)*(p+q) := by positivity
  have hnorm : T^(s+1) ≤ Q^(s+1)*J^(s+1) := by
    dsimp [T]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans hH) hHJ _) (pow_nonneg (zero_le_one.trans hQ) _)
  calc
    _ ≤ 2*C0*(T^(s+1)*A^(-eta)) +
        (CM+1)*(p*(T^(s+1)*A^(-eta))+q*(T^(s+1)*A^(-eta))) :=
      add_le_add hlocal (mul_le_mul_of_nonneg_left (add_le_add hcol hmod) (by linarith))
    _ = (2*C0+(CM+1)*(p+q))*(T^(s+1)*A^(-eta)) := by ring
    _ ≤ (2*C0+(CM+1)*(p+q))*((Q^(s+1)*J^(s+1))*A^(-eta)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnorm hAeta) hconst
    _ = _ := by ring

end Luce.Section6
