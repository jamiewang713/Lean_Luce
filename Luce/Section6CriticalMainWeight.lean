import Luce.Section6CriticalProbeBrackets
import Luce.Section6CriticalRemainingExpectation
import Luce.Section6PopulationPowerBounds

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem critical_exceptional_weight_absorption {gamma : ℝ} (hg : 0 < gamma) :
    ∃ D : ℝ, 0 < D ∧ ∀ n m : ℝ, 0 ≤ n → 0 < m → n ≤ m^2 →
      n^2*Real.exp (-(gamma*m)) ≤ D*n/m := by
  obtain ⟨D,hD,hbound⟩ := exponential_le_power (a := 3) (by norm_num) hg
  refine ⟨D,hD,?_⟩
  intro n m hn hm hnm
  have he : Real.exp (-(gamma*m)) ≤ D/m^3 := by
    simpa only [Real.rpow_neg hm.le,show (3 : ℝ) = (3 : ℕ) by norm_num,
      Real.rpow_natCast,div_eq_mul_inv] using hbound m hm
  calc
    _ ≤ n^2*(D/m^3) := mul_le_mul_of_nonneg_left he (sq_nonneg n)
    _ ≤ (n*m^2)*(D/m^3) := mul_le_mul_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_left hnm hn]) (by positivity)
    _ = _ := by field_simp

/-- A first-moment approximation sufficient for the critical CLT. The
power cutoff n ≤ m² lets the coarse exponential tail be absorbed directly. -/
theorem CriticalProfile.main_remaining_expectation {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ K Z : ℝ, 0 < K ∧ 1 ≤ Z ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (k : Fin n), 4 ≤ k.val+1 → (n : ℝ) ≤ ((k.val : ℝ)+1)^2 →
      Z ≤ Real.log ((n : ℝ)/((k.val : ℝ)+1)) →
      (∫ e, criticalRemainingWeight (w n) k e ∂exponentialRace (w n)) ≤
        c*n*Real.log ((n : ℝ)/((k.val : ℝ)+1))+
          K*n*(1+Real.log (Real.log ((n : ℝ)/((k.val : ℝ)+1)))+
            Real.log ((n : ℝ)/((k.val : ℝ)+1))/((k.val : ℝ)+1)) := by
  obtain ⟨C,hC,hprobe⟩ := hp.probe_estimates
  obtain ⟨Z,hZ,hbracket⟩ := hp.probe_brackets
  obtain ⟨a,b,ha,hb,hrates⟩ := hp.sampled_global_comparison
  obtain ⟨D,hD,htail⟩ := critical_exceptional_weight_absorption log_two_sub_half_pos
  have hc : 0 < c := hp.2.2.1
  let l : ℝ := 1/(16*c)
  have hl : 0 < l := by dsimp [l]; positivity
  let K := c+(C+c*|Real.log l|)+2*Real.exp (-1)/l+b*D
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,max Z l,hK,hZ.trans (le_max_left _ _),?_⟩
  intro grid w hw n k hk hnkm hz
  let m : ℝ := (k.val : ℝ)+1
  let z : ℝ := Real.log ((n : ℝ)/m)
  have hm : 0 < m := by dsimp [m]; positivity
  have hn : 0 < n := Nat.zero_lt_of_lt k.isLt
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hz1 : 1 ≤ z := hZ.trans ((le_max_left _ _).trans hz)
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hlz : l ≤ z := (le_max_right _ _).trans hz
  have hmeans := hbracket grid w hw n (k.val+1) hk k.isLt (by
    simpa only [Nat.cast_add,Nat.cast_one] using (le_max_left Z l).trans hz)
  have hmean : (n : ℝ)*populationG (w n) (criticalProbeTime n (k.val+1) l) ≤ m/2 := by
    simpa only [Nat.cast_add,Nat.cast_one] using hmeans.1
  have ht : 0 < criticalProbeTime n (k.val+1) l := by
    dsimp [criticalProbeTime]
    simp only [Nat.cast_add,Nat.cast_one]
    exact div_pos (mul_pos hl (div_pos hm hn0)) hz0
  have hE := critical_remaining_expectation_upper (w n) k ht.le hmean
  have hP := (hprobe grid w hw n (k.val+1) (by omega) k.isLt l hl
    (by simpa only [Nat.cast_add,Nat.cast_one] using hlz)).2
  simp only [Nat.cast_add,Nat.cast_one] at hP
  change (n : ℝ)*populationD (w n) 1 (criticalProbeTime n (k.val+1) l) ≤
    c*n*(z+Real.log z-Real.log l)+C*n+2*Real.exp (-1)*n*z/(l*m) at hP
  have htotal : (w n).total Finset.univ ≤ b*(n : ℝ)^2 := by
    calc
      _ ≤ ∑ _i : Fin n, b*n := by
        unfold Weights.total
        apply Finset.sum_le_sum
        intro i _
        exact (hrates grid w hw n i).2.trans
          (div_le_self (mul_nonneg hb.le hn0.le) (by have := Nat.cast_nonneg (α := ℝ) i.val; linarith))
      _ = _ := by simp; ring
  have hbad : (w n).total Finset.univ*Real.exp (-((Real.log 2-1/2)*m)) ≤ b*D*n/m := by
    calc
      _ ≤ (b*(n : ℝ)^2)*Real.exp (-((Real.log 2-1/2)*m)) :=
        mul_le_mul_of_nonneg_right htotal (Real.exp_pos _).le
      _ = b*((n : ℝ)^2*Real.exp (-((Real.log 2-1/2)*m))) := by ring
      _ ≤ b*(D*n/m) := mul_le_mul_of_nonneg_left (htail n m hn0.le hm hnkm) hb.le
      _ = _ := by ring
  let F := 1+Real.log z+z/m
  have hF1 : 1 ≤ F := by dsimp [F]; have := Real.log_nonneg hz1; have := div_pos hz0 hm; linarith
  have hFl : Real.log z ≤ F := by dsimp [F]; have := div_pos hz0 hm; linarith
  have hFz : z/m ≤ F := by dsimp [F]; have := Real.log_nonneg hz1; linarith
  have hFm : 1/m ≤ F := (div_le_div_of_nonneg_right hz1 hm.le).trans hFz
  have hlog : -(c*Real.log l) ≤ c*|Real.log l| := by
    simpa only [mul_neg] using mul_le_mul_of_nonneg_left (neg_le_abs (Real.log l)) hc.le
  have hcoeff : c*Real.log z+(C+c*|Real.log l|)+(2*Real.exp (-1)/l)*(z/m)+(b*D)*(1/m) ≤ K*F := by
    calc
      _ ≤ c*F+(C+c*|Real.log l|)*F+(2*Real.exp (-1)/l)*F+(b*D)*F := by
        exact add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hFl hc.le)
          (le_mul_of_one_le_right (by positivity) hF1))
          (mul_le_mul_of_nonneg_left hFz (by positivity)))
          (mul_le_mul_of_nonneg_left hFm (mul_pos hb hD).le)
      _ = _ := by dsimp [K]; ring
  change _ ≤ c*n*z+K*n*F
  have hraw := hE.trans (add_le_add hP hbad)
  have hlogn := mul_le_mul_of_nonneg_right hlog hn0.le
  have hcoeffn := mul_le_mul_of_nonneg_left hcoeff hn0.le
  ring_nf at hraw hlogn hcoeffn ⊢
  linarith only [hraw,hlogn,hcoeffn]

end Luce.Section6
