import Luce.Section6DeletedQuantileSeparation
import Luce.Section6RelativeMeanSeparation
import Luce.Section6GapTimeRelativeTail

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Left quantile-window tails with every deleted-mean premise derived
from the sampled profile. The explicit numerical window/deletion condition
must still be supplied by the final choice of the lower endpoint cutoff. -/
theorem PowerProfile.left_gap_quantile_window {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ a delta M : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m r : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ q : Fin (Finset.univ \ removed).card, |(q.val : ℝ)-(m : ℝ)| ≤ r →
    ∀ u : ℝ, 0 < u → u ≤ 1/2 → 8*(r : ℝ) ≤ a*u*m →
      let lo := (1-u)*leftQuantileTime (w n) m
      let hi := (1+u)*leftQuantileTime (w n) m
      (exponentialRace (w n)).real {old | raceGapStart (compactDeletedClocks removed old) q < lo} ≤
        Real.exp (-(a*u/8)^2*((n : ℝ)*deletedG (w n) removed lo)/4) ∧
      (exponentialRace (w n)).real {old | hi < raceGapStart (compactDeletedClocks removed old) q} ≤
        Real.exp (-(a*u/8)^2*((n : ℝ)*deletedG (w n) removed hi)/4) := by
  obtain ⟨a, delta, M, ha, ha1, hd, hM, hsep⟩ := hp.left_deleted_quantile_separation
  refine ⟨a, delta, M, ha, ha1, hd, hM, ?_⟩
  intro grid w hw n m r hm hmn hlarge hsmall removed hr q hq u hu hu1 hbudget
  have hs := hsep grid w hw n m r hm hmn hlarge hsmall removed hr u hu hu1
  have hv : 0 ≤ a*u := (mul_pos ha hu).le
  have hv1 : a*u ≤ 1 := (mul_le_mul_of_nonneg_right ha1 hu.le).trans (by linarith)
  have hh := relative_mean_separation (Nat.cast_nonneg m) hv hv1
    (show (r : ℝ) ≤ (a*u)*(m : ℝ)/8 by linarith only [hbudget]) hq hs.1 hs.2
  have ht := (leftQuantileTime_spec (w n) hm hmn).1
  have he : 0 ≤ a*u/8 := div_nonneg hv (by norm_num)
  have he1 : a*u/8 ≤ 1 := by linarith only [hv1]
  dsimp only
  exact ⟨deleted_gap_start_relative_early_arrival (w n) (hm.trans hmn) removed q
      (mul_nonneg (by linarith : 0 ≤ 1-u) ht.le) he he1 hh.1,
    deleted_gap_start_relative_late_arrival (w n) (hm.trans hmn) removed q
      (mul_nonneg (by linarith : 0 ≤ 1+u) ht.le) he he1 hh.2⟩

/-- Right quantile-window tails use survivor depth N-q. All population
separation premises are discharged from the original right profile. -/
theorem PowerProfile.right_gap_quantile_window {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ a delta M : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m r : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ q : Fin (Finset.univ \ removed).card,
      |((Finset.univ \ removed).card : ℝ)-(q.val : ℝ)-(m : ℝ)| ≤ r →
    ∀ u : ℝ, 0 < u → u ≤ 1/2 → 8*(r : ℝ) ≤ a*u*m →
      let lo := (1-u)*rightQuantileTime (w n) m
      let hi := (1+u)*rightQuantileTime (w n) m
      (exponentialRace (w n)).real {old | raceGapStart (compactDeletedClocks removed old) q < lo} ≤
        Real.exp (-(a*u/8)^2*((n : ℝ)*deletedH (w n) removed lo)/4) ∧
      (exponentialRace (w n)).real {old | hi < raceGapStart (compactDeletedClocks removed old) q} ≤
        Real.exp (-(a*u/8)^2*((n : ℝ)*deletedH (w n) removed hi)/4) := by
  obtain ⟨a, delta, M, ha, ha1, hd, hM, hsep⟩ := hp.right_deleted_quantile_separation
  refine ⟨a, delta, M, ha, ha1, hd, hM, ?_⟩
  intro grid w hw n m r hm hmn hlarge hsmall removed hr q hq u hu hu1 hbudget
  have hs := hsep grid w hw n m r hm hmn hlarge hsmall removed hr u hu hu1
  have hv : 0 ≤ a*u := (mul_pos ha hu).le
  have hv1 : a*u ≤ 1 := (mul_le_mul_of_nonneg_right ha1 hu.le).trans (by linarith)
  have hh := relative_mean_separation (Nat.cast_nonneg m) hv hv1
    (show (r : ℝ) ≤ (a*u)*(m : ℝ)/8 by linarith only [hbudget]) hq hs.2 hs.1
  have ht := (rightQuantileTime_spec (w n) hm hmn).1
  have he : 0 ≤ a*u/8 := div_nonneg hv (by norm_num)
  have he1 : a*u/8 ≤ 1 := by linarith only [hv1]
  dsimp only
  exact ⟨deleted_gap_start_relative_early_survivor (w n) (hm.trans hmn) removed q
      (mul_nonneg (by linarith : 0 ≤ 1-u) ht.le) he he1 hh.2,
    deleted_gap_start_relative_late_survivor (w n) (hm.trans hmn) removed q
      (mul_nonneg (by linarith : 0 ≤ 1+u) ht.le) he he1 hh.1⟩

end Luce.Section6
