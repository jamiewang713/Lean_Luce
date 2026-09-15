import Luce.Section6QuantileMoments

noncomputable section
open Set
namespace Luce.Section6

/-- Relative variation from exact finite derivatives and proved moment bounds. -/
theorem populationD_relative_variation {n : ℕ} (hn : 0 < n) (w : Weights n)
    {a C m t s : ℝ} (ha : 0 < a) (hC : 0 < C) (hm : 0 < m) (ht : 0 < t)
    (hcenter : a*m/t ≤ (n : ℝ)*populationD w 1 t)
    (hsecond : ∀ x ∈ Icc (t/4) (4*t), (n : ℝ)*populationD w 2 x ≤ C*m/t^2)
    (hs : s ∈ Icc (t/4) (4*t)) :
    |populationD w 1 s/populationD w 1 t-1| ≤ (C/a)*|s-t|/t := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hd : 0 < populationD w 1 t := populationD_pos hn w 1 t
  have hv : 0 < (n : ℝ)*populationD w 1 t := mul_pos hnR hd
  have hderiv (x : ℝ) (_hx : x ∈ Icc (t/4) (4*t)) :
      HasDerivWithinAt (fun y => (n : ℝ)*populationD w 1 y)
        ((n : ℝ)*(-populationD w 2 x)) (Icc (t/4) (4*t)) x :=
    ((populationD_hasDerivAt w 1 x).const_mul (n : ℝ)).hasDerivWithinAt
  have hnorm (x : ℝ) (hx : x ∈ Icc (t/4) (4*t)) :
      ‖(n : ℝ)*(-populationD w 2 x)‖ ≤ C*m/t^2 := by
    rw [mul_neg, norm_neg, Real.norm_eq_abs,
      abs_of_pos (mul_pos hnR (populationD_pos hn w 2 x))]
    exact hsecond x hx
  have hdiff := (convex_Icc (t/4) (4*t)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hnorm (show t ∈ Icc (t/4) (4*t) by constructor <;> linarith) hs
  simp only [Real.norm_eq_abs] at hdiff
  have heq : populationD w 1 s/populationD w 1 t-1 =
      ((n : ℝ)*populationD w 1 s-(n : ℝ)*populationD w 1 t)/
        ((n : ℝ)*populationD w 1 t) := by field_simp
  rw [heq, abs_div, abs_of_pos hv]
  apply (div_le_iff₀ hv).mpr
  have hcoef : 0 ≤ (C/a)*|s-t|/t := by positivity
  have hlow := mul_le_mul_of_nonneg_left hcenter hcoef
  have halg : ((C/a)*|s-t|/t)*(a*m/t) = (C*m/t^2)*|s-t| := by field_simp
  rw [halg] at hlow
  exact hdiff.trans hlow

theorem populationD_relative_stability {n : ℕ} (hn : 0 < n) (w : Weights n)
    {a C m t u : ℝ} (ha : 0 < a) (hC : 0 < C) (hm : 0 < m) (ht : 0 < t)
    (hu : 0 < u) (hu' : u ≤ 1/2)
    (hcenter : a*m/t ≤ (n : ℝ)*populationD w 1 t)
    (hsecond : ∀ x ∈ Icc (t/4) (4*t), (n : ℝ)*populationD w 2 x ≤ C*m/t^2) :
    |populationD w 1 ((1+u)*t)/populationD w 1 t-1| ≤ (C/a)*u ∧
    |populationD w 1 ((1-u)*t)/populationD w 1 t-1| ≤ (C/a)*u := by
  have hp := populationD_relative_variation hn w ha hC hm ht hcenter hsecond
    (show (1+u)*t ∈ Icc (t/4) (4*t) by constructor <;> nlinarith)
  have hm' := populationD_relative_variation hn w ha hC hm ht hcenter hsecond
    (show (1-u)*t ∈ Icc (t/4) (4*t) by constructor <;> nlinarith)
  have ep : |(1+u)*t-t| = u*t := by rw [abs_of_nonneg (by nlinarith)]; ring
  have em : |(1-u)*t-t| = u*t := by rw [abs_of_nonpos (by nlinarith)]; ring
  have ec : (C/a)*(u*t)/t = (C/a)*u := by field_simp
  rw [ep, ec] at hp
  rw [em, ec] at hm'
  exact ⟨hp, hm'⟩

/-- The manuscript's relative weight stability, with every moment premise derived. -/
theorem PowerProfile.right_quantile_weight_stability {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ K delta M : ℝ, 0 < K ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := rightQuantileTime (w n) m
      ∀ u : ℝ, 0 < u → u ≤ 1/2 →
        |populationD (w n) 1 ((1+u)*t)/populationD (w n) 1 t-1| ≤ K*u ∧
        |populationD (w n) 1 ((1-u)*t)/populationD (w n) 1 t-1| ≤ K*u := by
  obtain ⟨a, C, delta, M, ha, hC, hd, hM, h⟩ := hp.right_quantile_moments
  refine ⟨C/a, delta, M, div_pos hC ha, hd, hM, ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  dsimp only
  intro u hu hu'
  have ht := (rightQuantileTime_spec (w n) hm hmn).1
  have hwin := h grid w hw n m hm hmn hlarge hsmall
  exact populationD_relative_stability (hm.trans hmn) (w n) ha hC
    (Nat.cast_pos.mpr hm) ht hu hu'
    (hwin _ (by linarith) (by linarith)).1
    (fun x hx => (hwin x hx.1 hx.2).2.2)

/-- The manuscript's relative weight stability, with every moment premise derived. -/
theorem PowerProfile.left_quantile_weight_stability {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ K delta M : ℝ, 0 < K ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := leftQuantileTime (w n) m
      ∀ u : ℝ, 0 < u → u ≤ 1/2 →
        |populationD (w n) 1 ((1+u)*t)/populationD (w n) 1 t-1| ≤ K*u ∧
        |populationD (w n) 1 ((1-u)*t)/populationD (w n) 1 t-1| ≤ K*u := by
  obtain ⟨a, C, delta, M, ha, hC, hd, hM, h⟩ := hp.left_quantile_moments
  refine ⟨C/a, delta, M, div_pos hC ha, hd, hM, ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  dsimp only
  intro u hu hu'
  have ht := (leftQuantileTime_spec (w n) hm hmn).1
  have hwin := h grid w hw n m hm hmn hlarge hsmall
  exact populationD_relative_stability (hm.trans hmn) (w n) ha hC
    (Nat.cast_pos.mpr hm) ht hu hu'
    (hwin _ (by linarith) (by linarith)).1
    (fun x hx => (hwin x hx.1 hx.2).2.2)

end Luce.Section6

