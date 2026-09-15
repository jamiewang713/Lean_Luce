import Luce.Section6TailSlack

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- All one-insertion estimates for the left corner, with one envelope
coefficient and a common tail exponent. Tail decay uses explicit manuscript
slack (d/4 and nuTail<=nu); the kernel itself is unchanged by this weakening.
The closed endpoint block inequalities include their boundary. -/
theorem PowerProfile.left_insertion_moments {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r p0 : ℕ) (hp0 : 0 < p0)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    ∃ C d nu nuTail H delta : ℝ,
      0 < C ∧ 0 < d ∧ 0 < nu ∧ 0 < nuTail ∧ nuTail ≤ nu ∧
      0 < H ∧ 0 < delta ∧ delta < 1 ∧
      (∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
        ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → (h : ℝ)/(n : ℝ) ≤ delta →
        ∀ removed : Finset (Fin n), removed.card ≤ r →
        ∀ i : Fin n, H ≤ ((i.val : ℝ)+1) → ((i.val : ℝ)+1)/(n : ℝ) ≤ delta →
        ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
        Nat.dist q.val (h-1) ≤ r+1 →
        eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
          (p : ℝ≥0∞) (exponentialRace (w n)) ≤
          ENNReal.ofReal (C*((((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ))*Real.exp (-d*((h : ℝ)/((i.val : ℝ)+1))^alpha)+
            if ((h : ℝ)/((i.val : ℝ)+1))^alpha ≤ (min ((i.val : ℝ)+1) (h : ℝ))^v then 0 else Real.exp (-d*(h : ℝ)^nu)))) ∧
      (∀ A : ℕ, 1 ≤ A →
        restrictedKernelSums (fun a h => exceptionalEnvelope alpha v d nu h a) A ≤
          C*Real.exp (-(d/4)*(A : ℝ)^nuTail) ∧
        restrictedKernelSums (fun a h => extremeTypicalEnvelope alpha v d h a h) A ≤
          C*Real.exp (-(d/4)*(A : ℝ)^nuTail)) := by
  obtain ⟨Cl, d, nu, H, delta, hCl, hd, hnu, hH, hdelta, hdelta1, hlp⟩ :=
    hp.left_insertion_Lp_envelope r p0 hp0 v hv hv1
  have hb : 0 < alpha := lt_trans zero_lt_one hp.2.2.1.2.1
  have hk : 0 < alpha*v/(alpha+v) := div_pos (mul_pos hb hv) (add_pos hb hv)
  obtain ⟨Ce, hCe, he⟩ := exceptionalEnvelope_transpose_restricted_sums hb hv hd hnu
  obtain ⟨Ct, hCt, ht⟩ := left_typical_extreme_restricted_sums hb hv hd
  let C := Cl+Ce+Ct
  let nuTail := min nu (alpha*v/(alpha+v))
  have hClC : Cl ≤ C := by dsimp [C]; linarith
  have hCeC : Ce ≤ C := by dsimp [C]; linarith
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  refine ⟨C, d, nu, nuTail, H, delta/2, by dsimp [C]; positivity,
    hd, hnu, lt_min hnu hk, min_le_left _ _, hH, half_pos hdelta,
    (half_lt_self hdelta).trans hdelta1, ?_, ?_⟩
  · intro grid w hw n h hn hhH hhsmall removed hremoved i hiH hismall q p hpp hpp0 hshift
    apply (hlp grid w hw n h hn hhH (hhsmall.trans_lt (half_lt_self hdelta)) removed hremoved i
      (hismall.trans_lt (half_lt_self hdelta)) q p hpp hpp0 hshift).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right hClC
    apply add_nonneg (by positivity)
    split_ifs <;> positivity
  · intro A hA
    have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
    constructor
    · have heA : restrictedKernelSums (fun a h => exceptionalEnvelope alpha v d nu h a) A ≤
        Ce*Real.exp (-(d/2)*(A : ℝ)^nu) := he A hA
      exact heA.trans (stretched_tail_mono hCe.le hCeC (by positivity) (by linarith)
        (min_le_left _ _) hAR)
    · exact (ht A hA).trans (stretched_tail_mono hCt.le hCtC (by positivity) le_rfl
        (min_le_right _ _) hAR)

/-- All one-insertion estimates for the right corner, with one envelope
coefficient and a common tail exponent. Tail decay uses explicit manuscript
slack (d/4 and nuTail<=nu); the kernel itself is unchanged by this weakening.
The closed endpoint block inequalities include their boundary. -/
theorem PowerProfile.right_insertion_moments {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r p0 : ℕ) (hp0 : 0 < p0)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    ∃ C d nu nuTail H delta : ℝ,
      0 < C ∧ 0 < d ∧ 0 < nu ∧ 0 < nuTail ∧ nuTail ≤ nu ∧
      0 < H ∧ 0 < delta ∧ delta < 1 ∧
      (∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
        ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → (h : ℝ)/(n : ℝ) ≤ delta →
        ∀ removed : Finset (Fin n), removed.card ≤ r →
        ∀ i : Fin n, H ≤ (terminalDepth i : ℝ) → (terminalDepth i : ℝ)/(n : ℝ) ≤ delta →
        ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
        Nat.dist q.val (n-h) ≤ r+1 →
        eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
          (p : ℝ≥0∞) (exponentialRace (w n)) ≤
          ENNReal.ofReal (C*((((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ))*Real.exp (-d*((terminalDepth i : ℝ)/(h : ℝ))^beta)+
            if ((terminalDepth i : ℝ)/(h : ℝ))^beta ≤ (min (terminalDepth i : ℝ) (h : ℝ))^v then 0 else Real.exp (-d*(terminalDepth i : ℝ)^nu)))) ∧
      (∀ A : ℕ, 1 ≤ A →
        restrictedKernelSums (fun a h => exceptionalEnvelope beta v d nu a h) A ≤
          C*Real.exp (-(d/4)*(A : ℝ)^nuTail) ∧
        restrictedKernelSums (fun a h => extremeTypicalEnvelope beta v d a h h) A ≤
          C*Real.exp (-(d/4)*(A : ℝ)^nuTail)) := by
  obtain ⟨Cl, d, nu, H, delta, hCl, hd, hnu, hH, hdelta, hdelta1, hlp⟩ :=
    hp.right_insertion_Lp_envelope r p0 hp0 v hv hv1
  have hb : 0 < beta := hp.2.2.2.1.2.1
  have hk : 0 < beta*v/(beta+v) := div_pos (mul_pos hb hv) (add_pos hb hv)
  obtain ⟨Ce, hCe, he⟩ := exceptionalEnvelope_restricted_sums hb hv hd hnu
  obtain ⟨Ct, hCt, ht⟩ := right_typical_extreme_restricted_sums hb hv hd
  let C := Cl+Ce+Ct
  let nuTail := min nu (beta*v/(beta+v))
  have hClC : Cl ≤ C := by dsimp [C]; linarith
  have hCeC : Ce ≤ C := by dsimp [C]; linarith
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  refine ⟨C, d, nu, nuTail, H, delta/2, by dsimp [C]; positivity,
    hd, hnu, lt_min hnu hk, min_le_left _ _, hH, half_pos hdelta,
    (half_lt_self hdelta).trans hdelta1, ?_, ?_⟩
  · intro grid w hw n h hn hhH hhsmall removed hremoved i hiH hismall q p hpp hpp0 hshift
    apply (hlp grid w hw n h hn hhH (hhsmall.trans_lt (half_lt_self hdelta)) removed hremoved i
      (hismall.trans_lt (half_lt_self hdelta)) q p hpp hpp0 hshift).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right hClC
    apply add_nonneg (by positivity)
    split_ifs <;> positivity
  · intro A hA
    have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
    constructor
    · have heA : restrictedKernelSums (fun a h => exceptionalEnvelope beta v d nu a h) A ≤
        Ce*Real.exp (-(d/2)*(A : ℝ)^nu) := he A hA
      exact heA.trans (stretched_tail_mono hCe.le hCeC (by positivity) (by linarith)
        (min_le_left _ _) hAR)
    · exact (ht A hA).trans (stretched_tail_mono hCt.le hCtC (by positivity) le_rfl
        (min_le_right _ _) hAR)

end Luce.Section6
