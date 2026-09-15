import Luce.Section6UniformMomentDecay

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Luce.Section6

/-- The manuscript moderate-region Lp envelope, uniform over 1<=p<=p0,
for the original deleted insertion kernel and both sampling grids. -/
theorem PowerProfile.left_moderate_insertion_Lp {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d H delta : ℝ, 0 < C ∧ 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n), ((i.val : ℝ)+1)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
    Nat.dist q.val (h-1) ≤ r+1 →
    ∀ nu : ℝ, nu ≤ 1 → ((h : ℝ)/((i.val : ℝ)+1))^alpha ≤ (min ((i.val : ℝ)+1) (h : ℝ))^nu →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*(((h : ℝ)/((i.val : ℝ)+1))^alpha/(h : ℝ))*Real.exp (-d*((h : ℝ)/((i.val : ℝ)+1))^alpha)) := by
  obtain ⟨B, d, H, delta, hB, hd, hH, hdelta, hdelta1, hm⟩ := hp.left_moderate_insertion_moment r
  have hp0R : (0 : ℝ) < p0 := Nat.cast_pos.mpr hp0
  have hfact : (0 : ℝ) < p0.factorial := Nat.cast_pos.mpr (Nat.factorial_pos p0)
  refine ⟨2*(p0.factorial : ℝ)*B, d/(p0 : ℝ), H, delta,
    by positivity, div_pos hd hp0R, hH, hdelta, hdelta1, ?_⟩
  intro grid w hw n h hn hhH hh hsmall removed hremoved i hi q p hpp hpp0 hshift nu hnu hmoderate
  apply deleted_kernel_eLpNorm_le_of_moment (w n) removed i q.val p (by omega) (by positivity)
  exact (hm grid w hw n h hn hhH hh hsmall removed hremoved i hi q p hpp hshift nu hnu hmoderate).trans
    (uniform_moment_decay hpp hpp0 hB.le (by positivity) hd.le (by positivity))

/-- The manuscript moderate-region Lp envelope, uniform over 1<=p<=p0,
for the original deleted insertion kernel and both sampling grids. -/
theorem PowerProfile.right_moderate_insertion_Lp {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C d H delta : ℝ, 0 < C ∧ 0 < d ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n h : ℕ, 0 < n → H ≤ (h : ℝ) → 8*r+8 ≤ h → (h : ℝ)/(n : ℝ) < delta →
    ∀ removed : Finset (Fin n), removed.card ≤ r →
    ∀ (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) < delta →
    ∀ (q : Fin (Finset.univ \ removed).card) (p : ℕ), 1 ≤ p → p ≤ p0 →
    Nat.dist q.val (n-h) ≤ r+1 →
    ∀ nu : ℝ, nu ≤ 1 → ((terminalDepth i : ℝ)/(h : ℝ))^beta ≤ (min (terminalDepth i : ℝ) (h : ℝ))^nu →
    eLpNorm (fun old => (deletedGapKernel (w n) removed old i q.val).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n)) ≤
      ENNReal.ofReal (C*(((terminalDepth i : ℝ)/(h : ℝ))^beta/(h : ℝ))*Real.exp (-d*((terminalDepth i : ℝ)/(h : ℝ))^beta)) := by
  obtain ⟨B, d, H, delta, hB, hd, hH, hdelta, hdelta1, hm⟩ := hp.right_moderate_insertion_moment r
  have hp0R : (0 : ℝ) < p0 := Nat.cast_pos.mpr hp0
  have hfact : (0 : ℝ) < p0.factorial := Nat.cast_pos.mpr (Nat.factorial_pos p0)
  refine ⟨2*(p0.factorial : ℝ)*B, d/(p0 : ℝ), H, delta,
    by positivity, div_pos hd hp0R, hH, hdelta, hdelta1, ?_⟩
  intro grid w hw n h hn hhH hh hsmall removed hremoved i hi q p hpp hpp0 hshift nu hnu hmoderate
  apply deleted_kernel_eLpNorm_le_of_moment (w n) removed i q.val p (by omega) (by positivity)
  exact (hm grid w hw n h hn hhH hh hsmall removed hremoved i hi q p hpp hshift nu hnu hmoderate).trans
    (uniform_moment_decay hpp hpp0 hB.le (by positivity) hd.le (by positivity))

end Luce.Section6
