import Luce.Section6CriticalProbabilitySplit

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Luce.Section6

theorem critical_corner_choice {Z delta : ℝ} (hZ : 1 ≤ Z) (hd : 0 < delta) :
    ∃ eps : ℝ, 0 < eps ∧ eps < 1 ∧ eps < delta ∧ Z ≤ -Real.log eps := by
  let eps := min (delta/2) (Real.exp (-Z)/2)
  have hp : 0 < eps := lt_min (by positivity) (by positivity)
  have h1 : eps ≤ delta/2 := min_le_left _ _
  have h2 : eps ≤ Real.exp (-Z)/2 := min_le_right _ _
  have he : Real.exp (-Z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hl := Real.log_le_log hp (show eps ≤ Real.exp (-Z) by linarith [Real.exp_pos (-Z)])
  rw [Real.log_exp] at hl
  exact ⟨eps,hp,by linarith,by linarith,by linarith⟩

/-- All three reference-row conditions are consequences of the critical
profile alone, uniformly for the two sampling grids. -/
theorem CriticalProfile.reference_rows {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ eps C : ℝ, 0 < eps ∧ eps < 1 ∧ 0 < C ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ᶠ n : ℕ in atTop,
        (∀ k, 0 ≤ criticalReference n (criticalLower n) (criticalUpper eps n) k ∧
          criticalReference n (criticalLower n) (criticalUpper eps n) k ≤ 1) ∧
        (∑ k ∈ Finset.range n, ∫ e,
          |(raceInteriorBernoulli (w n) 1).toProcess.probability k e-
            criticalReference n (criticalLower n) (criticalUpper eps n) k| ∂exponentialRace (w n)) ≤ C ∧
        |(∑ k ∈ Finset.range n, criticalReference n (criticalLower n) (criticalUpper eps n) k)-
          Real.log (Real.log n)| ≤ C ∧
        (∑ k ∈ Finset.range n, (criticalReference n (criticalLower n) (criticalUpper eps n) k)^2) ≤ C := by
  obtain ⟨K,Z,delta,hK,hZ,hd,hd1,hmain⟩ := critical_main_block_error_sum hp
  obtain ⟨E,T,hE,hT,henv⟩ := hp.predictable_envelope
  obtain ⟨eps,heps,heps1,hepsd,hepsZ⟩ := critical_corner_choice
    (Z := max Z T) (by have := le_max_left Z T; linarith) hd
  obtain ⟨L,hL,hlate⟩ := hp.late_vertex_expectation 0 (eps := eps/2) (by positivity)
  have heta : 0 < eta := hp.2.2.2.1
  let C := 8*E+K*(12+1/eta)+L+2+(1+Real.log 4+2/eps)
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have htwo : 0 < 2/eps := by positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨eps,C,heps,heps1,hC,?_⟩
  intro grid w hw
  filter_upwards [critical_cutoffs_eventually heps heps1] with n hn
  rcases hn with ⟨hA,hAB,hBn,hAsq,hlogA,hBlo,hBhi,hlogn⟩
  let A := criticalLower n
  let B := criticalUpper eps n
  have hA1 : 1 ≤ A := by dsimp [A]; omega
  have hAp : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hBp : (0 : ℝ) < B := hAp.trans_le (by exact_mod_cast hAB)
  have hnp : (0 : ℝ) < n := hBp.trans_le (by exact_mod_cast hBn)
  have hzB : max Z T ≤ Real.log (n : ℝ)-Real.log (B : ℝ) := by
    have hh := Real.log_le_log hBp hBhi
    rw [Real.log_mul heps.ne' hnp.ne'] at hh
    linarith
  have hzZ : Z ≤ Real.log (n : ℝ)-Real.log (B : ℝ) := (le_max_left _ _).trans hzB
  have hzT : T ≤ Real.log (n : ℝ)-Real.log (B : ℝ) := (le_max_right _ _).trans hzB
  have hz1 : 1 ≤ Real.log (n : ℝ)-Real.log (B : ℝ) := by linarith
  have hBd : (B : ℝ)/(n : ℝ) < delta :=
    ((div_le_iff₀ hnp).mpr hBhi).trans_lt hepsd
  have hmain' := hmain grid w hw n A B hA hAB hBn hAsq hzZ hBd
  have hearly : (∑ k ∈ criticalBlock n 1 A, ∫ e,
      predictableChance (w n) (raceRankPermutation e).symm k ∂exponentialRace (w n)) ≤ 8*E := by
    apply critical_early_sum_bound hA1 (hAB.trans hBn) hlogn hlogA hE.le
    intro k hk
    have hkm := (Finset.mem_filter.mp hk).2
    have hz := hzT.trans (critical_block_log_lower (by omega : 1 ≤ 1)
      (k := k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkm.1,hkm.2.trans hAB⟩))
    calc
      _ ≤ ∫ _e, E/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1))) ∂exponentialRace (w n) := by
        apply integral_mono_ae (integrable_race_permutation_statistic (w n)
          (fun π => predictableChance (w n) π.symm k)) (integrable_const _)
        exact ae_of_all _ fun e => (henv grid w hw n (raceRankPermutation e).symm k hz).2
      _ = _ := by simp
  have hlate' : (∑ k ∈ criticalBlock n (B+1) n, ∫ e,
      predictableChance (w n) (raceRankPermutation e).symm k ∂exponentialRace (w n)) ≤ L := by
    rw [critical_predictable_sum_expectation]
    apply hlate grid w hw
    intro k hk
    have hkm := (Finset.mem_filter.mp hk).2.1
    apply (le_div_iff₀ hnp).mpr
    have hmB : (B : ℝ) ≤ (k.val : ℝ)+1 := by exact_mod_cast (show B ≤ k.val+1 by omega)
    linarith
  have herr := (critical_probability_reference_error (w n) hAB).trans
    (add_le_add (add_le_add hearly hmain') hlate')
  have hmass : |(∑ k ∈ Finset.range n, criticalReference n A B k)-Real.log (Real.log n)| ≤
      1+Real.log 4+2/eps := by
    rw [critical_reference_row_mass hA1 hAB hBn]
    exact critical_reference_mass_bound hnp heps hA1 hAB hlogn hlogA hz1 hBlo
  have hsq : (∑ k ∈ Finset.range n, (criticalReference n A B k)^2) ≤ 2 := by
    rw [critical_reference_row_sum n A B (fun x => x^2) (by norm_num)]
    exact critical_block_square_sum hA1 hAB hBn hz1
  refine ⟨critical_reference_row_bounds hA1 hAB hBn hz1,?_,?_,?_⟩
  · apply herr.trans
    dsimp [C]
    linarith
  · apply hmass.trans
    dsimp [C]
    have : 0 ≤ K*(12+1/eta) := by positivity
    linarith
  · apply hsq.trans
    dsimp [C]
    have : 0 ≤ K*(12+1/eta) := by positivity
    linarith

end Luce.Section6
