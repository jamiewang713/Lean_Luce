import Luce.Section6ModerateDecay

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

/-- Moderate-region moments of the literal deleted insertion kernel. Constants
are obtained from the original profile; the moderate-set condition describes
only which depth pairs this estimate addresses. -/
theorem PowerProfile.left_moderate_insertion_moment {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r : ℕ) :
    ∃ B d H delta : ℝ, 0 < B ∧ 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n), ((i.val : ℝ)+1)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p →
    Nat.dist q.val (h-1) ≤ r+1 →
    ∀ nu : ℝ, nu ≤ 1 → ((h : ℝ)/((i.val : ℝ)+1))^alpha ≤ (min ((i.val : ℝ)+1) (h : ℝ))^nu →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      2*(p.factorial : ℝ)*(B*(((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ)))^p*Real.exp (-d*((h : ℝ)/((i.val : ℝ)+1))^alpha) := by
  obtain ⟨B, d, H, delta, hB, hd, hH, hdelta, hdelta1, hm⟩ := hp.left_insertion_exponential_moment r
  refine ⟨B, d, H, delta, hB, hd, hH, hdelta, hdelta1, ?_⟩
  intro grid w hw n h hn hhH hh hsmall removed hremoved i hi q p hpp hshift nu hnu hmoderate
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have haR : (1 : ℝ) ≤ (i.val : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) i.val]
  have he := moderate_exponential_sum_le haR hhR hnu hmoderate hd.le
  apply (hm grid w hw n h hn hhH hh hsmall removed hremoved i hi q p hpp hshift).trans
  calc
    _ ≤ (p.factorial : ℝ)*(B*(((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ)))^p*(2*Real.exp (-d*((h : ℝ)/((i.val : ℝ)+1))^alpha)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/-- Moderate-region moments of the literal deleted insertion kernel. Constants
are obtained from the original profile; the moderate-set condition describes
only which depth pairs this estimate addresses. -/
theorem PowerProfile.right_moderate_insertion_moment {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r : ℕ) :
    ∃ B d H delta : ℝ, 0 < B ∧ 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p →
    Nat.dist q.val (n-h) ≤ r+1 →
    ∀ nu : ℝ, nu ≤ 1 → ((terminalDepth i : ℝ)/(h : ℝ))^beta ≤ (min (terminalDepth i : ℝ) (h : ℝ))^nu →
    (∫ old, (deletedGapKernel (w n) removed old i q.val).toReal^p ∂exponentialRace (w n)) ≤
      2*(p.factorial : ℝ)*(B*(((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ)))^p*Real.exp (-d*((terminalDepth i : ℝ)/(h : ℝ))^beta) := by
  obtain ⟨B, d, H, delta, hB, hd, hH, hdelta, hdelta1, hm⟩ := hp.right_insertion_exponential_moment r
  refine ⟨B, d, H, delta, hB, hd, hH, hdelta, hdelta1, ?_⟩
  intro grid w hw n h hn hhH hh hsmall removed hremoved i hi q p hpp hshift nu hnu hmoderate
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have haR : (1 : ℝ) ≤ terminalDepth i := by exact_mod_cast (terminalDepth_pos i)
  have he := moderate_exponential_sum_le haR hhR hnu hmoderate hd.le
  apply (hm grid w hw n h hn hhH hh hsmall removed hremoved i hi q p hpp hshift).trans
  calc
    _ ≤ (p.factorial : ℝ)*(B*(((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ)))^p*(2*Real.exp (-d*((terminalDepth i : ℝ)/(h : ℝ))^beta)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

end Luce.Section6
