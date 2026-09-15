import Luce.Section6CriticalProfileBounds
import Luce.Section6FastErrorExponent
import Luce.Section6KernelPerturbation
import Luce.Section6PositivePowerSumUpper
import Luce.Section6PopulationFinite

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace Luce.Section6

/-- The critical profile differs from its pole by an integrable power,
uniformly on the whole open unit interval. -/
theorem CriticalProfile.global_error_bound {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ e C : ℝ, 0 < e ∧ e ≤ 1/2 ∧ 0 < C ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, |f s-c/s| ≤ C*s^(e-1) := by
  let e := min eta (1/2)
  have he : 0 < e := lt_min hp.2.2.2.1 (by norm_num)
  have he1 : e ≤ 1/2 := min_le_right _ _
  have hex := hp.2.2.2.2.1.mono_error_exponent (min_le_left eta (1/2))
  obtain ⟨C,hC,hnear⟩ := hex.absolute_error_bound hp.2.2.1
  obtain ⟨delta,hd,hdelta⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  change 0 < delta at hd
  obtain ⟨a,b,ha,hb,hglob⟩ := hp.global_comparison
  refine ⟨e,max C ((b+c)/delta),he,he1,hC.trans_le (le_max_left _ _),?_⟩
  intro s hs
  have hc : 0 < c := hp.2.2.1
  have hpow : 0 < s^(e-1) := Real.rpow_pos_of_pos hs.1 _
  by_cases hsd : s < delta
  · have h := hdelta ⟨hs.1,hsd⟩
    simp only [Real.rpow_neg_one,← div_eq_mul_inv] at h
    have heq : -1+min eta (1/2) = e-1 := by dsimp [e]; ring
    rw [heq] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le)
  · have hf := (hp.2.1 s hs).le
    have hcs : 0 ≤ c/s := div_nonneg hc.le hs.1.le
    have hab : |f s-c/s| ≤ (b+c)/s := by
      calc
        _ ≤ |f s|+|c/s| := abs_sub _ _
        _ = f s+c/s := by rw [abs_of_nonneg hf,abs_of_nonneg hcs]
        _ ≤ b/s+c/s := add_le_add (hglob s hs).2 le_rfl
        _ = _ := by ring
    have hbound : |f s-c/s| ≤ (b+c)/delta := hab.trans
      (div_le_div_of_nonneg_left (by positivity) hd (le_of_not_gt hsd))
    have hone : 1 ≤ s^(e-1) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs.1 hs.2.le (by linarith)
    exact hbound.trans ((le_mul_of_one_le_right (by positivity) hone).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow.le))

/-- Both permitted grids have uniformly bounded averages of every
integrable negative power. -/
theorem critical_sampled_power_sum {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (grid : SamplingGrid) {n : ℕ} (hn : 0 < n) :
    (∑ i : Fin n, (samplePoint grid n i)^(e-1))/(n : ℝ) ≤
      (1/2 : ℝ)^(e-1)*(2+1/e) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have havg : (∑ i : Fin n, ((((i.val : ℝ)+1)/(n : ℝ))^(e-1)))/(n : ℝ) ≤
      2+1/e := by
    have hs := positive_power_sum_upper (z := e-1) (by linarith) n hn
    rw [sub_add_cancel] at hs
    have hsum : (∑ i : Fin n, ((((i.val : ℝ)+1)/(n : ℝ))^(e-1)))/(n : ℝ) =
        (∑ k ∈ Finset.range n, ((k : ℝ)+1)^(e-1))/(n : ℝ)^e := by
      have hdiv (i : Fin n) : ((((i.val : ℝ)+1)/(n : ℝ))^(e-1)) =
          ((i.val : ℝ)+1)^(e-1)/(n : ℝ)^(e-1) :=
        Real.div_rpow (by positivity) hn0.le _
      simp_rw [hdiv]
      rw [← Finset.sum_div,show (∑ i : Fin n, ((i.val : ℝ)+1)^(e-1)) =
        ∑ k ∈ Finset.range n, ((k : ℝ)+1)^(e-1) from
          Fin.sum_univ_eq_sum_range (fun k : ℕ => ((k : ℝ)+1)^(e-1)) n,div_div]
      congr 1
      calc
        (n : ℝ)^(e-1)*n = (n : ℝ)^((e-1)+1) := by rw [Real.rpow_add hn0,Real.rpow_one]
        _ = _ := by rw [sub_add_cancel]
    rw [hsum]
    have hne : 0 < (n : ℝ)^e := Real.rpow_pos_of_pos hn0 _
    have hpow : 1 ≤ (n : ℝ)^e := Real.one_le_rpow hnr he.le
    have hpow' : (n : ℝ)^(e-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hnr (by linarith)
    apply (div_le_iff₀ hne).mpr
    calc
      _ ≤ (n : ℝ)^e/e+1+(n : ℝ)^(e-1) := hs
      _ ≤ (n : ℝ)^e/e+2*(n : ℝ)^e := by linarith
      _ = _ := by ring
  calc
    _ ≤ (∑ i : Fin n, (1/2 : ℝ)^(e-1)*((((i.val : ℝ)+1)/(n : ℝ))^(e-1)))/n := by
      apply div_le_div_of_nonneg_right _ hn0.le
      apply Finset.sum_le_sum
      intro i _
      have hh := Real.rpow_le_rpow_of_nonpos (by positivity :
          0 < (1/2 : ℝ)*(((i.val : ℝ)+1)/(n : ℝ)))
        (samplePoint_ge_half_label grid i) (by linarith : e-1 ≤ 0)
      rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1/2) (by positivity)] at hh
    _ = (1/2 : ℝ)^(e-1)*((∑ i : Fin n, ((((i.val : ℝ)+1)/(n : ℝ))^(e-1)))/n) := by
      rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left havg (Real.rpow_nonneg (by norm_num) _)

/-- Uniform finite-population L¹ comparison with the exact pole. -/
theorem CriticalProfile.sampled_error_average {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (grid : SamplingGrid) (w : WeightArray),
      SampledRates grid w f → ∀ (n : ℕ), 0 < n →
      (∑ i : Fin n, |(w n).rate i-c/(samplePoint grid n i)|)/(n : ℝ) ≤ C := by
  obtain ⟨e,C,he,he1,hC,hbound⟩ := hp.global_error_bound
  refine ⟨C*((1/2 : ℝ)^(e-1)*(2+1/e)),by positivity,?_⟩
  intro grid w hw n hn
  calc
    _ ≤ (∑ i : Fin n, C*(samplePoint grid n i)^(e-1))/n := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact Finset.sum_le_sum fun i _ => by rw [hw n i]; exact hbound _ (samplePoint_mem grid i)
    _ = C*((∑ i : Fin n, (samplePoint grid n i)^(e-1))/n) := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (critical_sampled_power_sum he (by linarith) grid hn) hC.le

end Luce.Section6
