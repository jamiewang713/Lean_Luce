import Luce.Section6SmallTimePopulation
import Luce.Section6LeftMeanEnvelope
import Luce.Section6GapStartTail
import Luce.Section6SurvivalSplit

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Middle-rank early-time probability control, for every permitted left
endpoint behavior and every deleted background. The arrival mean is proved. -/
theorem PowerProfile.interior_gap_start_lower_tail {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ s N rho : ℝ, 0 < s ∧ 0 < N ∧ 0 < rho ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (removed : Finset (Fin n)) (q : Fin (Finset.univ \ removed).card),
    eps*(n : ℝ) ≤ (q.val : ℝ) →
    (exponentialRace (w n)).real {old | raceGapStart (compactDeletedClocks removed old) q < s} ≤
      Real.exp (-rho*(n : ℝ)) := by
  obtain ⟨s, N, hs, hs1, hN, hmean⟩ := hp.small_time_populationG (half_pos heps)
  have hc := log_two_sub_half_pos
  refine ⟨s, N, (Real.log 2-1/2)*eps, hs, hN, mul_pos hc heps, ?_⟩
  intro grid w hw n hn hlarge removed q hq
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hg := (deletedG_le_populationG (w n) removed hs.le).trans (hmean grid w hw n hn hlarge)
  have hm : (n : ℝ)*deletedG (w n) removed s ≤ (q.val : ℝ)/2 := by
    nlinarith [mul_le_mul_of_nonneg_left hg hnR.le]
  apply (deleted_gap_start_tail_of_arrival_mean (w n) hn removed q hs.le hm).trans
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hq hc.le]

/-- Interior survival expectation control for every marked source label.
No upper or lower source-rate assumption is needed at this step. -/
theorem PowerProfile.interior_survival_envelope {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ d N : ℝ, 0 < d ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (removed : Finset (Fin n)) (i : Fin n) (q : Fin (Finset.univ \ removed).card) (p : ℕ),
    eps*(n : ℝ) ≤ (q.val : ℝ) → 1 ≤ p →
    (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*raceGapStart (compactDeletedClocks removed old) q))
      ∂exponentialRace (w n)) ≤ Real.exp (-d*(w n).rate i)+Real.exp (-d*(n : ℝ)) := by
  obtain ⟨s, N, rho, hs, hN, hrho, htail⟩ := hp.interior_gap_start_lower_tail heps
  refine ⟨min s rho, N, lt_min hs hrho, hN, ?_⟩
  intro grid w hw n hn hlarge removed i q p hq hpp
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hpp
  have hi := (w n).positive i
  have he : Real.exp (-((p : ℝ)*(w n).rate i*s)) ≤ Real.exp (-(min s rho)*(w n).rate i) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left s rho) hi.le,
      mul_le_mul_of_nonneg_right hpR (mul_pos hi hs).le]
  have ht := (htail grid w hw n hn hlarge removed q hq).trans
    (Real.exp_le_exp.mpr (show -rho*(n : ℝ) ≤ -(min s rho)*(n : ℝ) by
      nlinarith [mul_le_mul_of_nonneg_right (min_le_right s rho) (Nat.cast_nonneg n)]))
  exact (deleted_survival_split (w n) removed i q p s).trans (add_le_add he ht)

end Luce.Section6
