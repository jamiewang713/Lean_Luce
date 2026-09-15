import Luce.Section6EnvelopeMonotonicity

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The combined manuscript insertion envelope with common constants on
both regions. The typical term is retained everywhere; the exceptional term
is present precisely on the complement of the moderate set. -/
theorem PowerProfile.left_insertion_Lp_envelope {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r p0 : ℕ) (hp0 : 0 < p0)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    ∃ C d nu H delta : ℝ, 0 < C ∧ 0 < d ∧ 0 < nu ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ i : Fin n, ((i.val : ℝ)+1)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
    Nat.dist q.val (h-1) ≤ r+1 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*((((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ))*Real.exp (-d*((h : ℝ)/((i.val : ℝ)+1))^alpha)+
        if ((h : ℝ)/((i.val : ℝ)+1))^alpha ≤ (min ((i.val : ℝ)+1) (h : ℝ))^v then 0 else Real.exp (-d*(h : ℝ)^nu))) := by
  obtain ⟨Cm, dm, Hm, dlm, hCm, hdm, hHm, hdlm, hdlm1, hm⟩ := hp.left_moderate_insertion_Lp r p0 hp0
  obtain ⟨Ce, de, nu, He, dle, hCe, hde, hnu, hHe, hdle, hdle1, he⟩ :=
    hp.left_extreme_insertion_Lp r p0 hp0 v hv
  let H := max (max Hm He) (8*(r : ℝ)+8)
  refine ⟨max Cm Ce, min dm de, nu, H, min dlm dle,
    hCm.trans_le (le_max_left _ _), lt_min hdm hde, hnu,
    hHm.trans_le ((le_max_left _ _).trans (le_max_left _ _)), lt_min hdlm hdle,
    (min_le_left _ _).trans_lt hdlm1, ?_⟩
  intro grid w hw n h hn hhH hsmall removed hremoved i hismall q p hpp hpp0 hshift
  have hh : 8*r+8 ≤ h := by
    have ht : 8*(r : ℝ)+8 ≤ (h : ℝ) := (le_max_right _ _).trans hhH
    exact_mod_cast ht
  have hhHm : Hm ≤ (h : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hhH
  have hhHe : He ≤ (h : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hhH
  have hx0 : 0 ≤ ((h : ℝ)/((i.val : ℝ)+1))^alpha := Real.rpow_nonneg (by positivity) _
  by_cases hmoderate : ((h : ℝ)/((i.val : ℝ)+1))^alpha ≤ (min ((i.val : ℝ)+1) (h : ℝ))^v
  · rw [if_pos hmoderate, add_zero]
    apply (hm grid w hw n h hn hhHm hh (hsmall.trans_le (min_le_left _ _)) removed hremoved i
      (hismall.trans_le (min_le_left _ _)) q p hpp hpp0 hshift v hv1 hmoderate).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using insertion_envelope_mono hCm.le (le_max_left _ _)
      (min_le_left _ _) (show 0 ≤ ((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ) by positivity) hx0
  · rw [if_neg hmoderate]
    have hb := he grid w hw n h hn hhHe hh (hsmall.trans_le (min_le_right _ _)) removed hremoved i
      (hismall.trans_le (min_le_right _ _)) q p hpp hpp0 hshift
      (by simpa only [min_comm] using hmoderate)
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    have hdec : Ce*Real.exp (-de*(h : ℝ)^nu) ≤ max Cm Ce*Real.exp (-(min dm de)*(h : ℝ)^nu) := by
      simpa only [mul_one] using insertion_envelope_mono hCe.le (le_max_right Cm Ce)
        (min_le_right dm de) (show (0 : ℝ) ≤ 1 by norm_num) (Real.rpow_nonneg (by positivity) nu)
    have hpos : 0 ≤ max Cm Ce*(((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ))*Real.exp (-(min dm de)*((h : ℝ)/((i.val : ℝ)+1))^alpha) := by positivity
    nlinarith only [hdec, hpos]

/-- The combined manuscript insertion envelope with common constants on
both regions. The typical term is retained everywhere; the exceptional term
is present precisely on the complement of the moderate set. -/
theorem PowerProfile.right_insertion_Lp_envelope {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r p0 : ℕ) (hp0 : 0 < p0)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    ∃ C d nu H delta : ℝ, 0 < C ∧ 0 < d ∧ 0 < nu ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ i : Fin n, (terminalDepth i : ℝ)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
    Nat.dist q.val (n-h) ≤ r+1 →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*((((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ))*Real.exp (-d*((terminalDepth i : ℝ)/(h : ℝ))^beta)+
        if ((terminalDepth i : ℝ)/(h : ℝ))^beta ≤ (min (terminalDepth i : ℝ) (h : ℝ))^v then 0 else Real.exp (-d*(terminalDepth i : ℝ)^nu))) := by
  obtain ⟨Cm, dm, Hm, dlm, hCm, hdm, hHm, hdlm, hdlm1, hm⟩ := hp.right_moderate_insertion_Lp r p0 hp0
  obtain ⟨Ce, de, nu, He, dle, hCe, hde, hnu, hHe, hdle, hdle1, he⟩ :=
    hp.right_extreme_insertion_Lp r p0 hp0 v hv
  let H := max (max Hm He) (8*(r : ℝ)+8)
  refine ⟨max Cm Ce, min dm de, nu, H, min dlm dle,
    hCm.trans_le (le_max_left _ _), lt_min hdm hde, hnu,
    hHm.trans_le ((le_max_left _ _).trans (le_max_left _ _)), lt_min hdlm hdle,
    (min_le_left _ _).trans_lt hdlm1, ?_⟩
  intro grid w hw n h hn hhH hsmall removed hremoved i hismall q p hpp hpp0 hshift
  have hh : 8*r+8 ≤ h := by
    have ht : 8*(r : ℝ)+8 ≤ (h : ℝ) := (le_max_right _ _).trans hhH
    exact_mod_cast ht
  have hhHm : Hm ≤ (h : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hhH
  have hhHe : He ≤ (h : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hhH
  have hx0 : 0 ≤ ((terminalDepth i : ℝ)/(h : ℝ))^beta := Real.rpow_nonneg (by positivity) _
  by_cases hmoderate : ((terminalDepth i : ℝ)/(h : ℝ))^beta ≤ (min (terminalDepth i : ℝ) (h : ℝ))^v
  · rw [if_pos hmoderate, add_zero]
    apply (hm grid w hw n h hn hhHm hh (hsmall.trans_le (min_le_left _ _)) removed hremoved i
      (hismall.trans_le (min_le_left _ _)) q p hpp hpp0 hshift v hv1 hmoderate).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using insertion_envelope_mono hCm.le (le_max_left _ _)
      (min_le_left _ _) (show 0 ≤ ((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ) by positivity) hx0
  · rw [if_neg hmoderate]
    have hb := he grid w hw n h hn hhHe hh (hsmall.trans_le (min_le_right _ _)) removed hremoved i
      (hismall.trans_le (min_le_right _ _)) q p hpp hpp0 hshift
      (by simpa only [min_comm] using hmoderate)
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    have hdec : Ce*Real.exp (-de*(terminalDepth i : ℝ)^nu) ≤ max Cm Ce*Real.exp (-(min dm de)*(terminalDepth i : ℝ)^nu) := by
      simpa only [mul_one] using insertion_envelope_mono hCe.le (le_max_right Cm Ce)
        (min_le_right dm de) (show (0 : ℝ) ≤ 1 by norm_num) (Real.rpow_nonneg (by positivity) nu)
    have hpos : 0 ≤ max Cm Ce*(((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ))*Real.exp (-(min dm de)*((terminalDepth i : ℝ)/(h : ℝ))^beta) := by positivity
    nlinarith only [hdec, hpos]

end Luce.Section6
