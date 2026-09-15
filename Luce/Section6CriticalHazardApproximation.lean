import Luce.Section6CriticalMainWeight
import Luce.Section6CriticalMainMissing
import Luce.Section6CriticalReciprocalError
import Luce.Section6CriticalPredictableEnvelope

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

/-- Summable L¹ error for the actual critical predictable hazard. The
reference still retains the sampled candidate rate; the last deterministic
profile expansion changes it to 1/(m log(n/m)). -/
theorem CriticalProfile.hazard_approximation {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ K Z : ℝ, 0 < K ∧ 1 ≤ Z ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (k : Fin n), 4 ≤ k.val+1 → (n : ℝ) ≤ ((k.val : ℝ)+1)^2 →
      Z ≤ Real.log ((n : ℝ)/((k.val : ℝ)+1)) →
      (∫ e, |predictableChance (w n) (raceRankPermutation e).symm k-
        (w n).rate k/(c*n*Real.log ((n : ℝ)/((k.val : ℝ)+1)))| ∂exponentialRace (w n)) ≤
      K/(((k.val : ℝ)+1)*Real.log ((n : ℝ)/((k.val : ℝ)+1)))*
        ((1+Real.log (Real.log ((n : ℝ)/((k.val : ℝ)+1))))/
          Real.log ((n : ℝ)/((k.val : ℝ)+1))+1/((k.val : ℝ)+1)) := by
  obtain ⟨C,hC,hfloor⟩ := hp.remaining_weight_floor
  obtain ⟨W,ZW,hW,hZW,hweight⟩ := hp.main_remaining_expectation
  obtain ⟨M,ZM,hM,hZM,hmissing⟩ := hp.main_missing_expectation
  obtain ⟨a,b,ha,hb,hrates⟩ := hp.sampled_global_comparison
  have hc : 0 < c := hp.2.2.1
  let B := M+2*(W+2*C)/c
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨(b/c)*B,max ZW (max ZM (2*C/c)),by positivity,
    hZW.trans (le_max_left _ _),?_⟩
  intro grid w hw n k hk hnkm hz
  let m : ℝ := (k.val : ℝ)+1
  let z : ℝ := Real.log ((n : ℝ)/m)
  let V := c*n*z
  let L := (n : ℝ)*(c*z-C)
  let F := 1+Real.log z+z/m
  let H := (1+Real.log z)/z+1/m
  have hm : 0 < m := by dsimp [m]; positivity
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt k.isLt)
  have hzW : ZW ≤ z := (le_max_left _ _).trans hz
  have hzM : ZM ≤ z := (le_max_left _ _).trans ((le_max_right _ _).trans hz)
  have hz1 : 1 ≤ z := hZW.trans hzW
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hzC : 2*C ≤ c*z := by
    have h := (le_max_right _ _).trans ((le_max_right _ _).trans hz)
    simpa only [mul_comm] using (div_le_iff₀ hc).mp h
  have hV : 0 < V := by dsimp [V]; positivity
  have hhalf : V/2 ≤ L := by
    dsimp [V,L]
    nlinarith [mul_le_mul_of_nonneg_left hzC hn0.le]
  have hL : 0 < L := (half_pos hV).trans_le hhalf
  have hLV : L ≤ V := by dsimp [L,V]; nlinarith [mul_nonneg hn0.le hC.le]
  have hLW (e : Fin n → ℝ) : L ≤ criticalRemainingWeight (w n) k e := by
    have h := hfloor grid w hw n (k.val+1) (by omega) k.isLt
      (Finset.univ \ remaining (raceRankPermutation e).symm k)
      (by rw [critical_drawn_card]; omega)
    rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] at h
    simpa only [L,z,m,criticalRemainingWeight,Weights.total,Nat.cast_add,Nat.cast_one] using h
  have hF1 : 1 ≤ F := by dsimp [F]; have := Real.log_nonneg hz1; have := div_pos hz0 hm; linarith
  have hH : 0 ≤ H := by dsimp [H]; have := Real.log_nonneg hz1; positivity
  have hFH : F/z = H := by dsimp [F,H]; field_simp
  have hMH : 1/z+1/m ≤ H := by
    dsimp [H]
    have h := div_nonneg (Real.log_nonneg hz1) hz0.le
    rw [add_div]
    linarith
  have hIM := (hmissing grid w hw n k hk hzM).trans
    (mul_le_mul_of_nonneg_left hMH hM.le)
  have hIW := hweight grid w hw n k hk hnkm hzW
  change (∫ e, criticalRemainingWeight (w n) k e ∂exponentialRace (w n)) ≤ V+W*n*F at hIW
  have hExcess : (∫ e, criticalRemainingWeight (w n) k e ∂exponentialRace (w n))+V-2*L ≤
      (n : ℝ)*(W+2*C)*F := by
    have hCF := mul_le_mul_of_nonneg_left hF1 (show 0 ≤ 2*C*n by positivity)
    dsimp [V,L] at *
    nlinarith only [hIW,hCF]
  have hU : 0 ≤ (n : ℝ)*(W+2*C)*F := by have := hF1; positivity
  have hθ : 0 < (w n).rate k := (w n).positive k
  have hcoeff : (w n).rate k/(L*V) ≤ 2*(w n).rate k/V^2 := by
    calc
      _ ≤ (w n).rate k/((V/2)*V) := div_le_div_of_nonneg_left hθ.le
        (mul_pos (half_pos hV) hV) (mul_le_mul_of_nonneg_right hhalf hV.le)
      _ = _ := by field_simp
  have href : (w n).rate k/V ≤ b/(c*m*z) := by
    calc
      _ ≤ (b*n/m)/V := div_le_div_of_nonneg_right (hrates grid w hw n k).2 hV.le
      _ = _ := by dsimp [V]; field_simp
  have heq : ((w n).rate k/V)*(M*H)+
      (2*(w n).rate k/V^2)*((n : ℝ)*(W+2*C)*F) = ((w n).rate k/V)*B*H := by
    rw [← hFH]
    dsimp [V,B]
    field_simp
  have hi := critical_predictable_integral_error (w n) k hL hLV hLW
  change _ ≤ ((b/c)*B)/(m*z)*H
  calc
    _ ≤ ((w n).rate k/V)*(∫ e, criticalMissingIndicator k e ∂exponentialRace (w n))+
        (w n).rate k/(L*V)*((∫ e, criticalRemainingWeight (w n) k e ∂exponentialRace (w n))+V-2*L) := hi
    _ ≤ ((w n).rate k/V)*(M*H)+(w n).rate k/(L*V)*((n : ℝ)*(W+2*C)*F) :=
      add_le_add (mul_le_mul_of_nonneg_left hIM (div_pos hθ hV).le)
        (mul_le_mul_of_nonneg_left hExcess (div_pos hθ (mul_pos hL hV)).le)
    _ ≤ ((w n).rate k/V)*(M*H)+(2*(w n).rate k/V^2)*((n : ℝ)*(W+2*C)*F) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoeff hU)
    _ = ((w n).rate k/V)*B*H := heq
    _ ≤ (b/(c*m*z))*B*H := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right href hB.le) hH
    _ = _ := by ring

end Luce.Section6
