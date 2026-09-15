import Luce.Section6LeftArrivalAsymptotic
import Luce.Section6InactiveBounds
import Luce.Section6JointErrorCutoffs
import Luce.Section6FiniteQuantiles

noncomputable section
namespace Luce.Section6

/-- Construct a fixed small time and a row cutoff for two positive powers. -/
theorem two_power_small_time {A K p q eps : ℝ}
    (hA : 0 < A) (hK : 0 < K) (hp : 0 < p) (hq : 0 < q) (he : 0 < eps) :
    ∃ s N : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 < N ∧
      ∀ n : ℝ, N ≤ n → A*s^p+K*(s^q+1/n) ≤ eps := by
  obtain ⟨delta, N, hd, hN, hb⟩ := joint_power_error_small
    (lt_min hp hq) (add_pos hA hK) he
  let s := min (delta/2) (1/2)
  have hs : 0 < s := lt_min (half_pos hd) (by norm_num)
  have hs1 : s ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hsd : s < delta := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨s, N, hs, hs1, hN, ?_⟩
  intro n hn
  have h1 := Real.rpow_le_rpow_of_exponent_ge hs hs1 (min_le_left p q)
  have h2 := Real.rpow_le_rpow_of_exponent_ge hs hs1 (min_le_right p q)
  have h3 := hb s n hs hsd hn
  have h4 : 0 ≤ 1/n := one_div_nonneg.mpr (hN.trans_le hn).le
  nlinarith [mul_le_mul_of_nonneg_left h1 hA.le,
    mul_le_mul_of_nonneg_left h2 hK.le, mul_nonneg hA.le h4]

theorem populationG_le_uniform_rate {n : ℕ} (hn : 0 < n) (w : Weights n)
    {M t : ℝ} (ht : 0 ≤ t) (hbound : ∀ i, w.rate i ≤ M) :
    populationG w t ≤ M*t := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold populationG
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑ _i : Fin n, M*t := Finset.sum_le_sum fun i _ => by
      have he := Real.add_one_le_exp (-(t*w.rate i))
      have hb := mul_le_mul_of_nonneg_left (hbound i) ht
      simp only [survivalKernel] at *
      rw [← neg_mul] at he
      nlinarith
    _ = _ := by simp; ring

/-- Uniform small-time arrival control derived from either allowed left
endpoint behavior. No integrability or normalization is assumed. -/
theorem PowerProfile.small_time_populationG {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (he : 0 < eps) :
    ∃ s N : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) → populationG (w n) s ≤ eps := by
  cases left with
  | finite c =>
    obtain ⟨M, hM, hb⟩ := hp.global_upper_of_left_finite
    let s := min (eps/M) 1
    have hs : 0 < s := lt_min (div_pos he hM) zero_lt_one
    refine ⟨s, 1, hs, min_le_right _ _, zero_lt_one, ?_⟩
    intro grid w hw n hn _
    have hbound : ∀ i, (w n).rate i ≤ M := by
      intro i
      rw [hw n i]
      exact hb _ (samplePoint_mem grid i)
    have hsmall : M*s ≤ eps := by
      have hh := mul_le_mul_of_nonneg_left (min_le_left (eps/M) 1) hM.le
      calc
        _ ≤ M*(eps/M) := hh
        _ = eps := by field_simp
    exact (populationG_le_uniform_rate hn (w n) hs.le hbound).trans hsmall
  | power c alpha eta =>
    have hc := hp.2.2.1.1
    have ha := hp.2.2.1.2.1
    have ha0 : 0 < alpha := zero_lt_one.trans ha
    have hg : 0 < 1-1/alpha := by
      have hh := one_div_lt_one_div_of_lt zero_lt_one ha
      rw [div_one] at hh
      linarith
    obtain ⟨eta', _, _, healpha, K, hK, herr⟩ := hp.left_populationG_power_error
    have hq : 0 < alpha-eta' := by linarith
    obtain ⟨s, N, hs, hs1, hN, hsmall⟩ := two_power_small_time
      (mul_pos (Real.Gamma_pos_of_pos hg) (Real.rpow_pos_of_pos hc (1/alpha)))
      hK (one_div_pos.mpr ha0) (one_div_pos.mpr hq) he
    refine ⟨s, N, hs, hs1, hN, ?_⟩
    intro grid w hw n hn hlarge
    have hh := (abs_le.mp (herr grid w hw n hn s hs hs1)).2
    have hb := hsmall (n : ℝ) hlarge
    linarith

/-- Both interior inverse populations stay away from time zero. -/
theorem PowerProfile.interior_quantile_time_lower {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (he : 0 < eps) :
    ∃ s N : ℝ, 0 < s ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ x : ℝ, eps ≤ x → x ≤ 1-eps →
      s ≤ arrivalQuantile (w n) x ∧ s ≤ survivorQuantile (w n) x := by
  obtain ⟨s, N, hs, _, hN, hb⟩ := hp.small_time_populationG he
  refine ⟨s, N, hs, hN, ?_⟩
  intro grid w hw n hn hlarge x hx hx'
  have hx0 : 0 ≤ x := (he.trans_le hx).le
  have hx1 : x < 1 := by linarith
  have hh := hb grid w hw n hn hlarge
  have hmono := populationG_strictMono hn (w n)
  constructor
  · apply hmono.le_iff_le.mp
    rw [populationG_arrivalQuantile hn (w n) ⟨hx0, hx1⟩]
    exact hh.trans hx
  · change s ≤ arrivalQuantile (w n) (1-x)
    apply hmono.le_iff_le.mp
    rw [populationG_arrivalQuantile hn (w n) ⟨by linarith, by linarith⟩]
    exact hh.trans (by linarith)

end Luce.Section6
