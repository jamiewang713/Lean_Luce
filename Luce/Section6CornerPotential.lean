import Luce.Section6FactorialKernelRows

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem corner_potential_pos (side : Corner) (kappa : ℝ) {a : ℕ} (ha : 0 < a) :
    0 < cornerDepthPotential side kappa a := by
  cases side <;> exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr ha) _

theorem corner_potential_quotient (side : Corner) (kappa : ℝ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    cornerDepthPotential side kappa b / cornerDepthPotential side kappa a =
      (cornerRowRatio side a b)^kappa := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  cases side with
  | left =>
    simp only [cornerDepthPotential, cornerRowRatio, Real.rpow_neg haR.le,
      Real.rpow_neg hbR.le, Real.div_rpow haR.le hbR.le]
    simp [div_eq_mul_inv, mul_comm]
  | right => exact (Real.div_rpow hbR.le haR.le kappa).symm

theorem corner_potential_ratio_power (side : Corner) (behavior : EndpointBehavior)
    {kappa : ℝ} (hg : 0 < localCornerExponent behavior) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (localCornerRatio side behavior a b)^(kappa/localCornerExponent behavior) =
      cornerDepthPotential side kappa a / cornerDepthPotential side kappa b := by
  rw [corner_potential_quotient side kappa hb ha]
  have hmul : localCornerExponent behavior*(kappa/localCornerExponent behavior) = kappa := by
    field_simp
  cases side <;> dsimp [localCornerRatio, cornerRowRatio]
  · rw [← Real.rpow_mul (by positivity), hmul]
  · rw [← Real.rpow_mul (by positivity), hmul]

theorem corner_weighted_row_to_potential {n : ℕ} (side : Corner) (kappa : ℝ)
    (F : Fin n → Fin n → ℝ) {C : ℝ}
    (hw : ∀ a, (∑ b, (cornerRowRatio side (cornerDistance side a) (cornerDistance side b))^kappa *
      F a b) ≤ C) (a : Fin n) :
    (∑ b, F a b*cornerDepthPotential side kappa (cornerDistance side b)) ≤
      C*cornerDepthPotential side kappa (cornerDistance side a) := by
  have hp := corner_potential_pos side kappa (cornerDistance_positive side a)
  have he (b : Fin n) :
      F a b*cornerDepthPotential side kappa (cornerDistance side b) =
        cornerDepthPotential side kappa (cornerDistance side a) *
          ((cornerRowRatio side (cornerDistance side a) (cornerDistance side b))^kappa * F a b) := by
    rw [← corner_potential_quotient side kappa (cornerDistance_positive side a) (cornerDistance_positive side b)]
    field_simp
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (hw a) hp.le).trans_eq (mul_comm _ _)

/-- A failure of the local moderation condition forces a polynomially
large potential ratio across that edge. -/
theorem nonmoderate_edge_has_large_potential (side : Corner) (behavior : EndpointBehavior)
    {a b A : ℕ} (hA : 1 ≤ A) (ha : A ≤ a) (hb : A ≤ b)
    {v kappa eta : ℝ} (hv : 0 < v) (hk : 0 < kappa)
    (hg : 0 < localCornerExponent behavior) (he : eta ≤ v*kappa/localCornerExponent behavior)
    (hbad : ¬ localCornerRatio side behavior a b ≤ (min (a : ℝ) (b : ℝ))^v) :
    (A : ℝ)^eta ≤ cornerDepthPotential side kappa a / cornerDepthPotential side kappa b := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hbase : (A : ℝ) ≤ min (a : ℝ) (b : ℝ) :=
    le_min (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hratio : (A : ℝ)^v ≤ localCornerRatio side behavior a b :=
    (Real.rpow_le_rpow hA0.le hbase hv.le).trans (le_of_lt (lt_of_not_ge hbad))
  have hpower := Real.rpow_le_rpow (Real.rpow_nonneg hA0.le v) hratio (div_pos hk hg).le
  rw [corner_potential_ratio_power side behavior hg ha0 hb0, ← Real.rpow_mul hA0.le] at hpower
  apply (Real.rpow_le_rpow_of_exponent_le hA1 he).trans
  convert hpower using 1 <;> congr 1 <;> ring

end Luce.Section6
