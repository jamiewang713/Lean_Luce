import Luce.Section6CriticalRetainedBound
import Luce.Section6CriticalReferenceBounds

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Luce.Section6

theorem critical_cycle_count_le {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ) :
    Section5.cycleCount R k ≤ n := by
  rw [← Section5.maximumCycleRoots_card]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)

theorem critical_cycle_expectation_le {n : ℕ} (w : Weights n) (k : ℕ) :
    (∫ e, (Section5.cycleCount (raceRankPermutation e) k : ℝ) ∂exponentialRace w) ≤ n := by
  have hh := integral_mono_ae (integrable_race_permutation_statistic w (fun R => (Section5.cycleCount R k : ℝ)))
    (integrable_const (n : ℝ)) (ae_of_all (exponentialRace w) fun e =>
      (show (Section5.cycleCount (raceRankPermutation e) k : ℝ) ≤ n by exact_mod_cast critical_cycle_count_le _ k))
  simpa using hh

/-- Every fixed cycle length at least two has uniformly bounded mean.
The lower cutoff is fixed, so cycles meeting its complement cost only
a fixed number of early labels plus the density-envelope tail bound. -/
theorem CriticalProfile.longer_cycle_race_bound {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ n, (∫ e, (Section5.cycleCount (raceRankPermutation e) k : ℝ) ∂exponentialRace (w n)) ≤ C := by
  obtain ⟨C,Z,hC,hZ,hroot⟩ := hp.critical_root_probability k hk
  obtain ⟨eps,heps,heps1,heps8,hepsZ⟩ := critical_corner_choice (Z := Z) (by linarith)
    (delta := (1/8 : ℝ)) (by norm_num)
  obtain ⟨L,hL,hlate⟩ := hp.late_vertex_expectation k (eps := eps/2) (by positivity)
  let M := 8*(k+1)+8
  have hgeom : ∀ᶠ n : ℕ in atTop, M ≤ criticalUpper eps n ∧
      criticalUpper eps n ≤ n ∧ eps*n/2 ≤ (criticalUpper eps n : ℝ) ∧
      (criticalUpper eps n : ℝ) ≤ eps*n := by
    have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    filter_upwards [critical_cutoffs_eventually heps heps1,hs.eventually_ge_atTop (M : ℝ)] with n hn hsM
    have hMA : M ≤ criticalLower n := by
      exact_mod_cast hsM.trans (Nat.le_ceil (Real.sqrt (n : ℝ)))
    exact ⟨hMA.trans hn.2.1,hn.2.2.1,hn.2.2.2.2.2.1,hn.2.2.2.2.2.2.1⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hgeom
  refine ⟨(N : ℝ)+M+3*C+L+1,by positivity,?_⟩
  intro grid w hw n
  by_cases hnN : N ≤ n
  · obtain ⟨hMB,hBn,hBlo,hBhi⟩ := hN n hnN
    let B := criticalUpper eps n
    have hM1 : 1 ≤ M := by dsimp [M]; omega
    have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hnp : (0 : ℝ) < n := hBp.trans_le (by exact_mod_cast hBn)
    have hB8 : 8*B ≤ n := by
      have h := mul_le_mul_of_nonneg_right heps8.le hnp.le
      exact_mod_cast (show 8*(B : ℝ) ≤ n by nlinarith)
    have hzB : Z ≤ Real.log (n : ℝ)-Real.log (B : ℝ) := by
      have hh := Real.log_le_log hBp hBhi
      rw [Real.log_mul heps.ne' hnp.ne'] at hh
      linarith
    have hretain := critical_retained_sum_bound (w n) k hM1 hMB hBn
      (by linarith : (3/2 : ℝ) ≤ Real.log (n : ℝ)-Real.log (B : ℝ)) hC.le
      (hroot grid w hw n M B le_rfl hB8 hzB)
    have hlate' : (∫ e, (exactCycleVertexCount (raceRankPermutation e) (k+1)
        (criticalBlock n (B+1) n) : ℝ) ∂exponentialRace (w n)) ≤ L := by
      apply hlate grid w hw
      intro i hi
      have hiB := (Finset.mem_filter.mp hi).2.1
      apply (le_div_iff₀ hnp).mpr
      have hBi : (B : ℝ) ≤ (i.val : ℝ)+1 := by exact_mod_cast (show B ≤ i.val+1 by omega)
      linarith
    have hiR := integrable_race_permutation_statistic (w n)
      (fun R => (Section5.cycleCountWithin R (criticalBlock n M B) k : ℝ))
    have hiL := integrable_race_permutation_statistic (w n)
      (fun R => (exactCycleVertexCount R (k+1) (criticalBlock n (B+1) n) : ℝ))
    have hiRM : Integrable (fun e => (Section5.cycleCountWithin (raceRankPermutation e) (criticalBlock n M B) k : ℝ)+M)
        (exponentialRace (w n)) := hiR.add (integrable_const _)
    have hh := integral_mono_ae (integrable_race_permutation_statistic (w n)
      (fun R => (Section5.cycleCount R k : ℝ))) (hiRM.add hiL)
      (ae_of_all (exponentialRace (w n)) fun e => (show
        (Section5.cycleCount (raceRankPermutation e) k : ℝ) ≤
          (Section5.cycleCountWithin (raceRankPermutation e) (criticalBlock n M B) k : ℝ)+M+
            (exactCycleVertexCount (raceRankPermutation e) (k+1) (criticalBlock n (B+1) n) : ℝ) by
        exact_mod_cast critical_cycle_count_split (raceRankPermutation e) k M B))
    simp only [Pi.add_apply] at hh
    rw [integral_add hiRM hiL,integral_add hiR (integrable_const _),integral_const] at hh
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hh
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith
  · have hh := critical_cycle_expectation_le (w n) k
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    linarith

end Luce.Section6
