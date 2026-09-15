import Luce.Section6FixedRightSurvival
import Luce.Section6UniformMomentDecay
import Luce.Section6DominationMatrixOutsideRight
import Luce.Section6StretchedExponentialSums

noncomputable section
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Fixed terminal matrix entries have summable source decay for every
row size and source depth, including the infinite final insertion gap. -/
theorem PowerProfile.domination_matrix_fixed_right_decay {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r H p : ℕ) (hp1 : 0 < p) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ i j : Fin n, terminalDepth j ≤ H →
      insertionDominationMatrix (w n) r p i j ≤
        C*Real.exp (-d*(terminalDepth i : ℝ)^(beta/(beta+1))) := by
  obtain ⟨d, A, N, hd, hA, hN, hb⟩ := hp.fixed_right_kernel_moment r H
  let z : ℝ := beta/(beta+1)
  have hz : 0 < z := (right_extreme_exponent_bounds hp.2.2.2.1.2.1).1
  let e : ℝ := d/(p : ℝ)
  have he : 0 < e := div_pos hd (Nat.cast_pos.mpr hp1)
  let T : ℝ := max A N
  let B : ℝ := 2*(p.factorial : ℝ)
  have hB : 0 < B := by dsimp [B]; positivity
  let C : ℝ := B+Real.exp (e*T^z)
  have hC : 0 < C := add_pos hB (Real.exp_pos _)
  refine ⟨C, e, hC, he, ?_⟩
  intro grid w hw n i j hj
  have hsmall : (terminalDepth i : ℝ) ≤ T →
      insertionDominationMatrix (w n) r p i j ≤ C*Real.exp (-e*(terminalDepth i : ℝ)^z) := by
    intro hiT
    have hexp : 1 ≤ Real.exp (e*T^z)*Real.exp (-e*(terminalDepth i : ℝ)^z) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have ht := Real.rpow_le_rpow (by positivity) hiT hz.le
      nlinarith [mul_le_mul_of_nonneg_left ht he.le]
    exact (insertionDominationMatrix_le_one (w n) r p i j).trans
      (hexp.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.exp_pos _).le))
  by_cases hnN : N ≤ (n : ℝ)
  · by_cases hiA : A ≤ (terminalDepth i : ℝ)
    · obtain ⟨removed, q, hremoved, hshift, hval⟩ := insertionDominationMatrix_attained (w n) r p i j
      have hm := hb grid w hw n hnN i j hiA hj removed hremoved q p hshift hp1
      have hfactor : (1 : ℝ) ≤ p.factorial := by exact_mod_cast Nat.factorial_pos p
      have hcoef : 2*Real.exp (-d*(terminalDepth i : ℝ)^z) ≤
          2*(p.factorial : ℝ)*(1*1)^p*Real.exp (-d*(terminalDepth i : ℝ)^z) := by
        simp only [one_mul, one_pow, mul_one]
        nlinarith [Real.exp_pos (-d*(terminalDepth i : ℝ)^z)]
      have hdec := uniform_moment_decay hp1 (le_refl p) (B := 1) (z := 1)
        zero_le_one zero_le_one hd.le (show 0 ≤ (terminalDepth i : ℝ)^z by positivity)
      have hnorm := deleted_kernel_eLpNorm_le_of_moment (w n) removed i q p hp1
        (show 0 ≤ B*Real.exp (-e*(terminalDepth i : ℝ)^z) by positivity)
        (hm.trans (hcoef.trans (by simpa only [B, e, mul_one] using hdec)))
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      rw [hval]
      exact hnorm.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [Real.exp_pos (e*T^z)]) (Real.exp_pos _).le))
    · exact hsmall ((le_of_not_ge hiA).trans (le_max_left _ _))
  · have hiN : (terminalDepth i : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n i.val)
    exact hsmall (hiN.trans ((le_of_not_ge hnN).trans (le_max_right _ _)))

/-- Uniform columns at every fixed terminal depth, including final gaps. -/
theorem PowerProfile.domination_matrix_fixed_right_column {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r H p : ℕ) (hp1 : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ j : Fin n, terminalDepth j ≤ H →
    ∀ s : Finset (Fin n), (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨B, d, hB, hd, hb⟩ := hp.domination_matrix_fixed_right_decay r H p hp1
  let z : ℝ := beta/(beta+1)
  have hz : 0 < z := (right_extreme_exponent_bounds hp.2.2.2.1.2.1).1
  have hs : Summable (fun a : ℕ => Real.exp (-d*(a : ℝ)^z)) := by
    simpa using summable_weighted_stretched_exp (b := 0) le_rfl hd hz
  let D : ℝ := max 1 (∑' a : ℕ, Real.exp (-d*(a : ℝ)^z))
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨B*D, mul_pos hB hD, ?_⟩
  intro grid w hw n j hj s
  have hinj : Function.Injective (terminalDepth : Fin n → ℕ) := by
    intro a b hab
    apply Fin.ext
    unfold terminalDepth at hab
    have := a.isLt
    have := b.isLt
    omega
  have hf := positive_depth_subset_sum_le s terminalDepth hinj
    (fun i => ⟨terminalDepth_pos i, Nat.sub_le _ _⟩)
    (fun a => Real.exp (-d*(a : ℝ)^z)) (fun _ _ => (Real.exp_pos _).le)
  have hsum : (∑ i ∈ s, Real.exp (-d*(terminalDepth i : ℝ)^z)) ≤ D :=
    hf.trans ((hs.sum_le_tsum (Finset.Ico 1 (n+1)) (fun _ _ => (Real.exp_pos _).le)).trans (le_max_right 1 _))
  calc
    _ ≤ ∑ i ∈ s, B*Real.exp (-d*(terminalDepth i : ℝ)^z) :=
      Finset.sum_le_sum (fun i _ => hb grid w hw n i j hj)
    _ = B*(∑ i ∈ s, Real.exp (-d*(terminalDepth i : ℝ)^z)) := (Finset.mul_sum _ _ _).symm
    _ ≤ B*D := mul_le_mul_of_nonneg_left hsum hB.le

/-- Complete active-right column bound, including all fixed terminal depths. -/
theorem PowerProfile.domination_matrix_right_column {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ j : Fin n, (terminalDepth j : ℝ)/(n : ℝ) ≤ delta →
    ∀ s : Finset (Fin n), (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨B, H, delta, hB, hH, hd, hd1, hb⟩ := hp.domination_matrix_right_column_above_cutoff r p hp1
  obtain ⟨H0, hH0⟩ := exists_nat_gt H
  obtain ⟨D, hD, he⟩ := hp.domination_matrix_fixed_right_column r H0 p hp1
  refine ⟨B+D, delta, add_pos hB hD, hd, hd1, ?_⟩
  intro grid w hw n j hj s
  by_cases hdepth : H ≤ (terminalDepth j : ℝ)
  · exact (hb grid w hw n j hdepth hj s).trans (by linarith)
  · have hjH : terminalDepth j ≤ H0 := by
      exact_mod_cast (lt_of_not_ge hdepth).le.trans hH0.le
    exact (he grid w hw n j hjH s).trans (by linarith)

end Luce.Section6
