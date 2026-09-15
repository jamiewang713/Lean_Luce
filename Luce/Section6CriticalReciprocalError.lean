import Luce.Section6CriticalMissingLabel

noncomputable section
open MeasureTheory
namespace Luce.Section6

theorem critical_reciprocal_error {theta W V L : ℝ} (hθ : 0 ≤ theta)
    (hL : 0 < L) (hW : L ≤ W) (hV : L ≤ V) :
    |theta/W-theta/V| ≤ theta/(L*V)*(W+V-2*L) := by
  have hw : 0 < W := hL.trans_le hW
  have hv : 0 < V := hL.trans_le hV
  have heq : theta/W-theta/V = theta*(V-W)/(W*V) := by field_simp
  have hab : |V-W| ≤ W+V-2*L := by rw [abs_le]; constructor <;> linarith
  have hn : 0 ≤ W+V-2*L := by linarith
  rw [heq,abs_div,abs_mul,abs_of_nonneg hθ,abs_of_pos (mul_pos hw hv)]
  calc
    _ ≤ theta*(W+V-2*L)/(W*V) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab hθ) (mul_pos hw hv).le
    _ ≤ theta*(W+V-2*L)/(L*V) := div_le_div_of_nonneg_left (mul_nonneg hθ hn)
      (mul_pos hL hv) (mul_le_mul_of_nonneg_right hW hv.le)
    _ = _ := by ring

/-- Pointwise reciprocal comparison uses only a one-sided denominator
floor; the excess remaining weight enters linearly. -/
theorem critical_predictable_error {n : ℕ} (w : Weights n) (k : Fin n) (e : Fin n → ℝ)
    {L V : ℝ} (hL : 0 < L) (hV : L ≤ V) (hW : L ≤ criticalRemainingWeight w k e) :
    |predictableChance w (raceRankPermutation e).symm k-w.rate k/V| ≤
      (w.rate k/V)*criticalMissingIndicator k e+
        w.rate k/(L*V)*(criticalRemainingWeight w k e+V-2*L) := by
  classical
  rw [predictableChance_formula,Equiv.symm_symm]
  change |(if k ≤ raceRankPermutation e k then w.rate k else 0)/criticalRemainingWeight w k e-
    w.rate k/V| ≤ _
  by_cases hp : k ≤ raceRankPermutation e k
  · simp only [if_pos hp,criticalMissingIndicator,mul_zero,zero_add]
    exact critical_reciprocal_error (w.positive k).le hL hW hV
  · simp only [if_neg hp,zero_div,zero_sub,abs_neg,criticalMissingIndicator,mul_one]
    rw [abs_of_pos (div_pos (w.positive k) (hL.trans_le hV))]
    have herr : 0 ≤ w.rate k/(L*V)*(criticalRemainingWeight w k e+V-2*L) :=
      mul_nonneg (div_nonneg (w.positive k).le (mul_pos hL (hL.trans_le hV)).le) (by linarith)
    linarith

theorem critical_predictable_integral_error {n : ℕ} (w : Weights n) (k : Fin n)
    {L V : ℝ} (hL : 0 < L) (hV : L ≤ V)
    (hW : ∀ e, L ≤ criticalRemainingWeight w k e) :
    (∫ e, |predictableChance w (raceRankPermutation e).symm k-w.rate k/V| ∂exponentialRace w) ≤
      (w.rate k/V)*(∫ e, criticalMissingIndicator k e ∂exponentialRace w)+
        w.rate k/(L*V)*((∫ e, criticalRemainingWeight w k e ∂exponentialRace w)+V-2*L) := by
  have hp := integrable_race_permutation_statistic w (fun π => |predictableChance w π.symm k-w.rate k/V|)
  have hM := integrable_race_permutation_statistic w (fun π => if k ≤ π k then (0 : ℝ) else 1)
  have hR : Integrable (criticalRemainingWeight w k) (exponentialRace w) :=
    integrable_race_permutation_statistic w (fun π => w.total (remaining π.symm k))
  have hRV : Integrable (fun e => criticalRemainingWeight w k e+V) (exponentialRace w) :=
    hR.add (integrable_const V)
  have hi : Integrable (fun e => criticalRemainingWeight w k e+V-2*L) (exponentialRace w) :=
    (hR.add (integrable_const _)).sub (integrable_const _)
  have h := integral_mono_ae hp ((hM.const_mul (w.rate k/V)).add (hi.const_mul (w.rate k/(L*V))))
    (Filter.Eventually.of_forall fun e => critical_predictable_error w k e hL hV (hW e))
  simp only [Pi.add_apply] at h
  rw [integral_add (hM.const_mul _) (hi.const_mul _),integral_const_mul,integral_const_mul,
    integral_sub hRV (integrable_const _),
    integral_add hR (integrable_const _),integral_const,integral_const] at h
  simpa [criticalMissingIndicator] using h

end Luce.Section6
