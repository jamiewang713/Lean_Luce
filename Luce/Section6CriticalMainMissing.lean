import Luce.Section6CriticalMissingLabel
import Luce.Section6CriticalProbeBrackets
import Luce.Section6PopulationPowerBounds

noncomputable section
open MeasureTheory
namespace Luce.Section6

theorem CriticalProfile.main_missing_expectation {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ K Z : ℝ, 0 < K ∧ 1 ≤ Z ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (k : Fin n), 4 ≤ k.val+1 →
      Z ≤ Real.log ((n : ℝ)/((k.val : ℝ)+1)) →
      (∫ e, criticalMissingIndicator k e ∂exponentialRace (w n)) ≤
        K*(1/Real.log ((n : ℝ)/((k.val : ℝ)+1))+1/((k.val : ℝ)+1)) := by
  obtain ⟨Z,hZ,hbracket⟩ := hp.probe_brackets
  obtain ⟨a,b,ha,hb,hrate⟩ := hp.sampled_global_comparison
  obtain ⟨E,hE,hExp⟩ := exponential_le_power (a := 1) (by norm_num) (d := 1/8) (by norm_num)
  have hc : 0 < c := hp.2.2.1
  refine ⟨8*b/c+E,Z,by positivity,hZ,?_⟩
  intro grid w hw n k hk hz
  let m : ℝ := (k.val : ℝ)+1
  let z : ℝ := Real.log ((n : ℝ)/m)
  have hm : 0 < m := by dsimp [m]; positivity
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt k.isLt)
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one (hZ.trans hz)
  have hmeans := (hbracket grid w hw n (k.val+1) hk k.isLt (by
    simpa only [Nat.cast_add,Nat.cast_one] using hz)).2
  simp only [Nat.cast_add,Nat.cast_one] at hmeans
  have ht : 0 < criticalProbeTime n (k.val+1) (8/c) := by
    dsimp [criticalProbeTime]
    simp only [Nat.cast_add,Nat.cast_one]
    exact div_pos (mul_pos (by positivity) (div_pos hm hn0)) hz0
  have hM := critical_missing_expectation_upper (w n) k ht.le hmeans
  have hrateT : (w n).rate k*criticalProbeTime n (k.val+1) (8/c) ≤ (8*b/c)*(1/z) := by
    calc
      _ ≤ (b*n/m)*criticalProbeTime n (k.val+1) (8/c) :=
        mul_le_mul_of_nonneg_right (hrate grid w hw n k).2 ht.le
      _ = _ := by
        dsimp [criticalProbeTime]
        simp only [Nat.cast_add,Nat.cast_one]
        change (b*n/m)*((8/c)*(m/n)/z) = _
        field_simp
  have hExp' : Real.exp (-m/8) ≤ E/m := by
    have h := hExp m hm
    rw [show -((1/8 : ℝ)*m) = -m/8 by ring,Real.rpow_neg_one] at h
    simpa only [div_eq_mul_inv] using h
  have hsum := hM.trans (add_le_add hrateT hExp')
  change _ ≤ (8*b/c+E)*(1/z+1/m)
  apply hsum.trans
  have h1 := mul_nonneg (show 0 ≤ 8*b/c by positivity) (show 0 ≤ 1/m by positivity)
  have h2 := mul_nonneg hE.le (show 0 ≤ 1/z by positivity)
  ring_nf at h1 h2 ⊢
  linarith

end Luce.Section6
