import Luce.Section6RightSurvivorRegion

noncomputable section
namespace Luce.Section6

/-- The survivor mean estimate at a real-valued comparison depth. This is
needed at the extreme scale a^(beta/(beta+1)); the actual row and deletion
set are unchanged. No mean condition is assumed. -/
theorem PowerProfile.right_early_deleted_mean_real_depth {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r : ℕ) :
    ∃ k H delta : ℝ, 0 < k ∧ k ≤ 1 ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) h, 0 < n → 0 < h → H ≤ h → h/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
      8*h ≤ (n : ℝ)*deletedH (w n) removed (k*((n : ℝ)/h)^beta) := by
  obtain ⟨S, M, hS, hM, hbound⟩ := hp.right_deletedH_lower_region r
  have hb : 0 < beta := hp.2.2.2.1.2.1
  let A := Real.Gamma (1+1/beta)*c^(-(1/beta))
  have hA : 0 < A := mul_pos (Real.Gamma_pos_of_pos (by positivity))
    (Real.rpow_pos_of_pos hp.2.2.2.1.1 _)
  let u := min (1 : ℝ) (A/16)
  have hu : 0 < u := lt_min zero_lt_one (div_pos hA (by norm_num))
  have hu1 : u ≤ 1 := min_le_left _ _
  have huA : 16*u ≤ A := by have := min_le_right (1 : ℝ) (A/16); dsimp [u]; linarith
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  let v := S^(1/beta)
  have hv : 0 < v := Real.rpow_pos_of_pos hS0 _
  let k := u^beta
  have hk : 0 < k := Real.rpow_pos_of_pos hu _
  refine ⟨k, M*u, min (1/2) (u/(2*v)), hk, Real.rpow_le_one hu.le hu1 hb.le,
    mul_pos hM hu, lt_min (by norm_num) (div_pos hu (by positivity)),
    (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro grid w hw n h hn hh hH hsmall removed hremoved
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := hh
  have hx : 0 < (n : ℝ)/h := div_pos hnR hhR
  have hvpow : v^beta = S := by
    dsimp [v]
    rw [← Real.rpow_mul hS0.le, show (1/beta)*beta = 1 by field_simp [ne_of_gt hb], Real.rpow_one]
  have hvx : v ≤ u*((n : ℝ)/h) := by
    have hh' := (div_lt_div_iff₀ hnR (by positivity : 0 < 2*v)).mp
      (hsmall.trans_le (min_le_right _ _))
    rw [show u*((n : ℝ)/h) = (u*(n : ℝ))/h by ring]
    apply (le_div_iff₀ hhR).mpr
    nlinarith [mul_pos hv hhR]
  have htS : S ≤ k*((n : ℝ)/h)^beta := by
    rw [← hvpow]
    have he : k*((n : ℝ)/h)^beta = (u*((n : ℝ)/h))^beta :=
      (Real.mul_rpow hu.le hx.le).symm
    rw [he]
    exact Real.rpow_le_rpow hv.le hvx hb.le
  have hpow : (k*((n : ℝ)/h)^beta)^(-(1/beta)) = h/(u*(n : ℝ)) := by
    dsimp [k]
    rw [← Real.mul_rpow hu.le hx.le, ← Real.rpow_mul (mul_nonneg hu.le hx.le),
      show beta*(-(1/beta)) = -1 by field_simp [ne_of_gt hb], Real.rpow_neg_one]
    field_simp [ne_of_gt hu, ne_of_gt hnR, ne_of_gt hhR]
  have hm : M ≤ (n : ℝ)*(k*((n : ℝ)/h)^beta)^(-(1/beta)) := by
    rw [hpow]
    have he : (n : ℝ)*(h/(u*(n : ℝ))) = h/u := by
      field_simp [ne_of_gt hu, ne_of_gt hnR]
    rw [he]
    exact (le_div_iff₀ hu).mpr hH
  have hmean := mul_le_mul_of_nonneg_left (hbound grid w hw n hn removed hremoved _ htS hm) hnR.le
  rw [hpow] at hmean
  have he : (n : ℝ)*((A*(h/(u*(n : ℝ))))/2) = (A/(2*u))*h := by
    field_simp [ne_of_gt hu, ne_of_gt hnR]
  change (n : ℝ)*((A*(h/(u*(n : ℝ))))/2) ≤ _ at hmean
  rw [he] at hmean
  apply le_trans _ hmean
  apply mul_le_mul_of_nonneg_right _ hhR.le
  apply (le_div_iff₀ (by positivity : 0 < 2*u)).mpr
  linarith

end Luce.Section6
