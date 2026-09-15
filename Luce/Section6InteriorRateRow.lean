import Luce.Section6InteriorInsertionLp

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Interior target rows retain the source rate. The natural gap index is
proved nonterminal from the constructed row-size margin. -/
theorem PowerProfile.interior_insertion_rate_row {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    {eps : ℝ} (heps : 0 < eps) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, eps*(n : ℝ) ≤ (j.val : ℝ)+1 ∧
      (j.val : ℝ)+1 ≤ (1-eps)*(n : ℝ) ∧
      (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal (C*(w n).rate i) := by
  obtain ⟨B, d, N, hB, hd, hN, hb⟩ := hp.interior_insertion_Lp heps r p0 hp0
  refine ⟨2*B, max N ((8*(r : ℝ)+8)/eps), by positivity,
    hN.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n hn hlarge i s removed q p hpp hpp0 hs
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi := (w n).positive i
  have hmargin : 8*(r : ℝ)+8 ≤ eps*(n : ℝ) := by
    have hh := (div_le_iff₀ heps).mp ((le_max_right _ _).trans hlarge)
    nlinarith
  have hterm : 0 ≤ (2*B)*(w n).rate i/(n : ℝ) := by positivity
  calc
    _ ≤ ∑ _j ∈ s, ENNReal.ofReal ((2*B)*(w n).rate i/(n : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hl, hu, hremoved, hshift⟩ := hs j hj
      have hbuffer : j.val+1+(2*r+2) ≤ n := by
        have hh : (j.val : ℝ)+1+(2*(r : ℝ)+2) ≤ n := by nlinarith
        exact_mod_cast hh
      have hcard : (Finset.univ \ removed j).card = n-(removed j).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have hq : q j < (Finset.univ \ removed j).card := by
        unfold Nat.dist at hshift
        omega
      have he := hb grid w hw n (j.val+1) hn ((le_max_left _ _).trans hlarge)
        (by simpa using hl) (by simpa using hu) (removed j) hremoved i ⟨q j, hq⟩ p
        (by simpa using hshift) hpp hpp0
      apply he.trans
      apply ENNReal.ofReal_le_ofReal
      have he1 : Real.exp (-d*(w n).rate i) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le) hi.le)
      have he2 : Real.exp (-d*(n : ℝ)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le) hnR.le)
      have hh := mul_le_mul_of_nonneg_left (add_le_add he1 he2)
        (show 0 ≤ B*((w n).rate i/(n : ℝ)) by positivity)
      calc
        _ ≤ B*((w n).rate i/(n : ℝ))*(1+1) := hh
        _ = _ := by ring
    _ = ENNReal.ofReal (∑ _j ∈ s, (2*B)*(w n).rate i/(n : ℝ)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ => hterm)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hc : (s.card : ℝ) ≤ n := by
        have hcN : s.card ≤ n := by simpa using s.card_le_univ
        exact_mod_cast hcN
      simp only [Finset.sum_const, nsmul_eq_mul]
      calc
        _ ≤ (n : ℝ)*((2*B)*(w n).rate i/(n : ℝ)) := mul_le_mul_of_nonneg_right hc hterm
        _ = _ := by field_simp

end Luce.Section6
