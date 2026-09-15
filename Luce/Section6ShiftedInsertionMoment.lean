import Luce.Section6DepthComparison

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Left insertion moment at full-rank depth h, uniformly for the manuscript's
bounded gap displacement. All rate and depth comparison premises are discharged. -/
theorem PowerProfile.left_shifted_insertion_moment {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ B delta : ℝ, 0 < B ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 0 < n → ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (h p : ℕ),
    8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ((i.val : ℝ)+1)/(n : ℝ) < delta → Nat.dist q.val (h-1) ≤ r+1 →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*(B*(((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ)))^p*
      (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*
        raceGapStart (compactDeletedClocks removed old) q)) ∂exponentialRace (w n)) := by
  obtain ⟨B, d, eps, hB, hd, hd1, heps, heps1, hmoment⟩ := hp.left_insertion_moment_reduction
  refine ⟨B*(2 : ℝ)^(alpha+1), min d (eps/8),
    mul_pos hB (Real.rpow_pos_of_pos (by norm_num) _),
    lt_min hd (div_pos heps (by norm_num)), (min_le_left _ _).trans_lt hd1, ?_⟩
  intro grid w hw n r hn removed hremoved i q h p hh hhn hi hshift
  obtain ⟨hq, hqh, hhq⟩ := shifted_left_gap_bounds hh hshift
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hqR : (0 : ℝ) < q.val := Nat.cast_pos.mpr (by omega)
  have hqhR : (q.val : ℝ) ≤ 2*(h : ℝ) := by exact_mod_cast hqh
  have hhqR : (h : ℝ) ≤ 2*(q.val : ℝ) := by exact_mod_cast hhq
  have hsmall := (div_lt_iff₀ hnR).mp (hhn.trans_le (min_le_right _ _))
  have hqsmall : (q.val : ℝ) ≤ eps*(n : ℝ)/4 := by nlinarith
  have hb := left_depth_factor_comparison (by positivity : 0 < (i.val : ℝ)+1)
    hqR hhR (by have := hp.2.2.1.2.1; linarith : 0 ≤ alpha) hqhR hhqR
  have hb' : B*(((q.val : ℝ)/((i.val : ℝ)+1))^alpha/(q.val : ℝ)) ≤
      (B*(2 : ℝ)^(alpha+1))*(((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ)) := by
    nlinarith only [mul_le_mul_of_nonneg_left hb hB.le]
  apply (hmoment grid w hw n r hn removed hremoved i q p hq hqsmall
    (hi.trans_le (min_le_left _ _))).trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · apply pow_le_pow_left₀ _ hb' p
      positivity
    · positivity
  · exact integral_nonneg (fun _ => (Real.exp_pos _).le)

/-- Right insertion moment at full terminal depth h, with bounded deletions
and gap displacement. The actual survivor count is proved comparable to h. -/
theorem PowerProfile.right_shifted_insertion_moment {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ B delta : ℝ, 0 < B ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n r : ℕ, 0 < n → ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n) (q : Fin (Finset.univ \ removed).card) (h p : ℕ),
    8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    (terminalDepth i : ℝ)/(n : ℝ) < delta → Nat.dist q.val (n-h) ≤ r+1 →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      (p.factorial : ℝ)*(B*(((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ)))^p*
      (∫ old, Real.exp (-((p : ℝ)*(w n).rate i*
        raceGapStart (compactDeletedClocks removed old) q)) ∂exponentialRace (w n)) := by
  obtain ⟨B, delta, hB, hd, hd1, hmoment⟩ := hp.right_insertion_moment_reduction
  refine ⟨B*(2 : ℝ)^(beta+1), delta, mul_pos hB (Real.rpow_pos_of_pos (by norm_num) _), hd, hd1, ?_⟩
  intro grid w hw n r hn removed hremoved i q h p hh hhn hi hshift
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hle : h ≤ n := by
    have ht := (div_lt_one hnR).mp (hhn.trans hd1)
    exact Nat.le_of_lt (Nat.cast_lt.mp ht)
  obtain ⟨hq, hhm, _⟩ := shifted_right_survivor_bounds hremoved hle hh hshift
  let m := n-removed.card-q.val
  have hm : 0 < m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hcount : m+removed.card+q.val ≤ n := by dsimp [m]; omega
  have hhmR : (h : ℝ) ≤ 2*(m : ℝ) := by exact_mod_cast hhm
  have hb := right_depth_factor_comparison (Nat.cast_pos.mpr (terminalDepth_pos i)) hmR hhR
    hp.2.2.2.1.2.1.le hhmR
  have hb' : B*(((terminalDepth i : ℝ)/(m : ℝ))^beta/(m : ℝ)) ≤
      (B*(2 : ℝ)^(beta+1))*(((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ)) := by
    nlinarith only [mul_le_mul_of_nonneg_left hb hB.le]
  apply (hmoment grid w hw n hn removed i q m p hm hcount hi).trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · apply pow_le_pow_left₀ _ hb' p
      positivity
    · positivity
  · exact integral_nonneg (fun _ => (Real.exp_pos _).le)

end Luce.Section6
