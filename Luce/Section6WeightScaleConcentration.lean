import Luce.Section6RemainingWeightVariance
import Luce.Section6QuantileMoments

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Deleting labels decreases each nonnegative finite rate moment. -/
theorem deletedD_le_populationD {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (k : ℕ) (t : ℝ) :
    deletedD w removed k t ≤ populationD w k t := by
  unfold deletedD populationD
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
  intro i _ _
  exact mul_nonneg (pow_nonneg (w.positive i).le _) (survivalKernel_pos _ _).le

/-- Chebyshev at the endpoint's natural weight scale m/t. The only
moment premise is discharged by the profile theorems below. -/
theorem deleted_weight_scaled_chebyshev {n : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) {s t m C eps : ℝ} (hs : 0 ≤ s)
    (ht : 0 < t) (hm : 0 < m) (heps : 0 < eps)
    (hsecond : (n : ℝ)*populationD w 2 s ≤ C*m/t^2) :
    (exponentialRace w).real {old | eps*m/t ≤ |(∑ i ∈ Finset.univ \ removed,
      w.rate i*clockSurvivalIndicator s i old)-(n : ℝ)*deletedD w removed 1 s|} ≤
        C/(eps^2*m) := by
  have hv : (n : ℝ)*deletedD w removed 2 s ≤ C*m/t^2 :=
    (mul_le_mul_of_nonneg_left (deletedD_le_populationD w removed 2 s) (Nat.cast_nonneg n)).trans hsecond
  calc
    _ ≤ (n : ℝ)*deletedD w removed 2 s / (eps*m/t)^2 :=
      deleted_remaining_weight_chebyshev w hn removed hs (div_pos (mul_pos heps hm) ht)
    _ ≤ (C*m/t^2)/(eps*m/t)^2 := div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ = C/(eps^2*m) := by field_simp

/-- Profile-derived right-endpoint weight concentration, uniform over
all deleted sets and fixed times in the quantile window. -/
theorem PowerProfile.right_weight_quantile_concentration {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ C delta M : ℝ, 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := rightQuantileTime (w n) m
      ∀ s : ℝ, t/4 ≤ s → s ≤ 4*t → ∀ removed : Finset (Fin n),
      ∀ eps : ℝ, 0 < eps →
        (exponentialRace (w n)).real {old | eps*(m : ℝ)/t ≤
          |(∑ i ∈ Finset.univ \ removed, (w n).rate i*clockSurvivalIndicator s i old)-
            (n : ℝ)*deletedD (w n) removed 1 s|} ≤ C/(eps^2*(m : ℝ)) := by
  obtain ⟨a, C, delta, M, ha, hC, hd, hM, h⟩ := hp.right_quantile_moments
  refine ⟨C, delta, M, hC, hd, hM, ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  dsimp only
  intro s hs hs' removed eps heps
  have ht := (rightQuantileTime_spec (w n) hm hmn).1
  exact deleted_weight_scaled_chebyshev (w n) (hm.trans hmn) removed
    (le_trans (by positivity : (0 : ℝ) ≤ rightQuantileTime (w n) m/4) hs)
    ht (Nat.cast_pos.mpr hm) heps (h grid w hw n m hm hmn hlarge hsmall s hs hs').2.2

/-- The same polynomial concentration scale at the left endpoint,
derived from the original left profile without bounded rates. -/
theorem PowerProfile.left_weight_quantile_concentration {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ C delta M : ℝ, 0 < C ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := leftQuantileTime (w n) m
      ∀ s : ℝ, t/4 ≤ s → s ≤ 4*t → ∀ removed : Finset (Fin n),
      ∀ eps : ℝ, 0 < eps →
        (exponentialRace (w n)).real {old | eps*(m : ℝ)/t ≤
          |(∑ i ∈ Finset.univ \ removed, (w n).rate i*clockSurvivalIndicator s i old)-
            (n : ℝ)*deletedD (w n) removed 1 s|} ≤ C/(eps^2*(m : ℝ)) := by
  obtain ⟨a, C, delta, M, ha, hC, hd, hM, h⟩ := hp.left_quantile_moments
  refine ⟨C, delta, M, hC, hd, hM, ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  dsimp only
  intro s hs hs' removed eps heps
  have ht := (leftQuantileTime_spec (w n) hm hmn).1
  exact deleted_weight_scaled_chebyshev (w n) (hm.trans hmn) removed
    (le_trans (by positivity : (0 : ℝ) ≤ leftQuantileTime (w n) m/4) hs)
    ht (Nat.cast_pos.mpr hm) heps (h grid w hw n m hm hmn hlarge hsmall s hs hs').2.2

end Luce.Section6
