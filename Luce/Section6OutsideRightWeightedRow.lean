import Luce.Section6RightOutsideKernelSum
import Luce.Section6RightOutsideEnvelope

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Outside-right sources: the actual moderate-target weighted row.
The source-block condition bounds the weight; all analytic inputs are derived. -/
theorem PowerProfile.outside_right_weighted_insertion_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta sigma kappa : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (hk : 0 ≤ kappa)
    (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C H delta N : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta ≤ 1/2 ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n), sigma ≤ (terminalDepth i : ℝ)/(n : ℝ) →
    ∀ (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n)) (q : Fin n → ℕ)
      (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, H ≤ (terminalDepth j : ℝ) ∧ (terminalDepth j : ℝ)/(n : ℝ) ≤ delta ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, d, H, delta, N, hB, hd, hH, hdelta, hdelta1, hN, hb⟩ :=
    hp.right_outside_insertion_envelope hsigma hsigma1 r p0 hp0
  have hbeta : 0 < beta := hp.2.2.2.1.2.1
  obtain ⟨D, hD, hsum⟩ := right_outside_kernel_subset_bound hbeta hd (right_extreme_exponent_bounds hbeta).1
  let W : ℝ := (1/sigma)^kappa
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨(W*B)*D, max H (8*(r : ℝ)+8), min (delta/2) (1/2), N,
    by positivity, hH.trans_le (le_max_left _ _), lt_min (half_pos hdelta) (by norm_num),
    min_le_right _ _, hN, ?_⟩
  intro grid w hw n hn hlarge i hi s removed q p hpp hpp0 hs
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ha : (0 : ℝ) < terminalDepth i := Nat.cast_pos.mpr (terminalDepth_pos i)
  have hir := (w n).positive i
  let F : Fin n → ℝ := fun j =>
    ((w n).rate i*((n : ℝ)/(terminalDepth j : ℝ))^beta/(terminalDepth j : ℝ))*
      Real.exp (-d*((w n).rate i*((n : ℝ)/(terminalDepth j : ℝ))^beta))+
      Real.exp (-d*(n : ℝ)^(beta/(beta+1)))
  have hF (j : Fin n) : 0 ≤ F j := by dsimp [F]; positivity
  have hfinite : (∑ j ∈ s, F j) ≤ D := by
    simpa only [F, neg_mul] using hsum n ((w n).rate i) hn hir s
  calc
    _ ≤ ∑ j ∈ s, ENNReal.ofReal ((W*B)*F j) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hjH, hjsmall, hremoved, hshift⟩ := hs j hj
      have hjrange : 8*r+8 ≤ terminalDepth j := by
        have hh := (le_max_right _ _).trans hjH
        exact_mod_cast hh
      have hjrank : n-terminalDepth j = j.val := by unfold terminalDepth; omega
      have hcard : (Finset.univ \ removed j).card = n-(removed j).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have hq : q j < (Finset.univ \ removed j).card := by
        rw [hcard]
        exact (shifted_right_survivor_bounds hremoved (Nat.sub_le _ _) hjrange
          (by change Nat.dist (q j) (n-terminalDepth j) ≤ r+1; rwa [hjrank])).1
      have he := hb grid w hw n (terminalDepth j) hn hlarge ((le_max_left _ _).trans hjH)
        hjrange ((hjsmall.trans (min_le_left _ _)).trans_lt (half_lt_self hdelta))
        (removed j) hremoved i hi ⟨q j, hq⟩ p hpp hpp0 (by simpa only [hjrank] using hshift)
      have he' : eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
          (p : ℝ≥0∞) (exponentialRace (w n)) ≤ ENNReal.ofReal (B*F j) := by
        simpa only [F] using he
      have hdepth : (terminalDepth j : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n j.val)
      have hratio : (terminalDepth j : ℝ)/(terminalDepth i : ℝ) ≤ 1/sigma := by
        apply (div_le_div_iff₀ ha hsigma).mpr
        have hi' := (le_div_iff₀ hnR).mp hi
        nlinarith [mul_le_mul_of_nonneg_left hdepth hsigma.le]
      have hweight := Real.rpow_le_rpow (by positivity) hratio hk
      have hm := mul_le_mul (ENNReal.ofReal_le_ofReal hweight) he' zero_le zero_le
      rw [← ENNReal.ofReal_mul hW.le] at hm
      simpa only [mul_assoc] using hm
    _ = ENNReal.ofReal ((W*B)*(∑ j ∈ s, F j)) := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (mul_pos hW hB).le (hF j))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hfinite (mul_pos hW hB).le)

end Luce.Section6
