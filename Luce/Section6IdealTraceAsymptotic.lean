import Luce.Section6IdealCollisions

noncomputable section
open MeasureTheory
namespace Luce.Section6

/-- A stronger total-trace estimate retains the common boundary constant.
This permits spatial traces to be obtained by subtracting nested intervals. -/
theorem logDistinctTrace68_refined {p : ℝ → ℝ} (hp : TraceDensity68 p)
    (hd : Differentiable ℝ p) {C g : ℝ} (hC : 0 < C) (hg : 0 < g)
    (hb : ∀ x, p x+‖deriv p x‖ ≤ C*Real.exp (-g*|x|)) (k : ℕ) :
    ∃ E D c : ℝ, 0 < E ∧ 0 < D ∧ 0 < c ∧ ∀ A B : ℕ, 1 ≤ A → A ≤ B →
      |logDistinctTrace68 p k A B-
        (traceConvolution68 p k 0/((k : ℝ)+1))*Real.log ((B : ℝ)/A)+cycleRangeMass68 p k| ≤
        E*((1+Real.log ((B : ℝ)/A))/(A : ℝ))+D*Real.exp (-c*Real.log ((B : ℝ)/A)) := by
  let b := traceConvolution68 p k 0/((k : ℝ)+1)
  let L := logCollisionConstant68 C g k
  let H := logGridErrorConstant68 C g k*logEnvelopeTraceBound68 g k/((k : ℝ)+1)
  let c := g/4
  let J := (∫ y : Fin k → ℝ, Real.exp (c*logTupleRange k (Fin.cons 0 y))*
    closedLogCycleWeight p k (Fin.cons 0 y))/(c*((k : ℝ)+1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hb0 : 0 ≤ b := div_nonneg (hp.convolution_nonneg k 0) (by positivity)
  have hL : 0 ≤ L := by dsimp [L, logCollisionConstant68]; positivity
  have hH : 0 ≤ H := by dsimp [H, logGridErrorConstant68, logEnvelopeTraceBound68]; positivity
  have hJ : 0 ≤ J := by
    apply div_nonneg _ (by positivity)
    exact integral_nonneg (fun y => mul_nonneg (Real.exp_pos _).le (closedLogCycleWeight_nonneg68 hp.nonneg _ _))
  have hpb (x : ℝ) : p x ≤ C*Real.exp (-g*|x|) := (le_add_of_nonneg_right (norm_nonneg _)).trans (hb x)
  have hE := cycle_exponential_moment68 hp hC.le hg hpb k
  refine ⟨L+H+b+1, J+1, c, by positivity, by positivity, hc, ?_⟩
  intro A B hA hAB
  have hAr : 0 < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hBr : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  let T := Real.log ((B : ℝ)/A)
  let T1 := Real.log ((B+1 : ℕ) : ℝ)-Real.log (A : ℝ)
  let d := logCellWidth68 B
  have hT : 0 ≤ T := Real.log_nonneg ((one_le_div hAr).mpr (by exact_mod_cast hAB))
  have hd0 : 0 ≤ d := (logCellWidth68_pos (by omega : 0 < B)).le
  have hdA : d ≤ 1/(A : ℝ) := (logCellWidth68_bounds (by omega : 0 < B)).2.trans
    (one_div_le_one_div_of_le hAr (by exact_mod_cast hAB))
  have hd1 : d ≤ 1 := hdA.trans ((one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
    (by exact_mod_cast hA)).trans_eq (by norm_num))
  have hT1 : T1 = T+d := by
    dsimp [T1,T,d,logCellWidth68]
    rw [Real.log_div hBr.ne' hAr.ne']
    ring
  have hT10 : 0 ≤ T1 := by rw [hT1]; positivity
  have hT1upper : T1 ≤ 1+T := by rw [hT1]; linarith
  have hcol := logDistinctTrace68_comparison hp.nonneg hC.le hg hpb k hA hAB
  have hgrid := logGridTrace68_comparison hp hd hC.le hg hb k hA hAB
  have hrel : |relativeIdealTrace68 p k T1-b*T1+cycleRangeMass68 p k| ≤ J*Real.exp (-c*T1) := by
    convert relativeIdealTrace68_remainder hp hc k hE hT10 using 1 <;>
      first | rfl | (congr 1; dsimp [b]; ring)
  have hexp : J*Real.exp (-c*T1) ≤ (J+1)*Real.exp (-c*T) := by
    apply mul_le_mul (by linarith) _ (Real.exp_pos _).le (by positivity)
    apply Real.exp_le_exp.mpr
    rw [hT1]
    nlinarith
  have hrel' := hrel.trans hexp
  have hbd : |b*d| ≤ b*(1/(A : ℝ)) := by
    rw [abs_of_nonneg (mul_nonneg hb0 hd0)]
    exact mul_le_mul_of_nonneg_left hdA hb0
  have hf : 0 ≤ (1+T)/(A : ℝ) := by positivity
  have hrem : L/(A : ℝ)+H*(T1/(A : ℝ))+b*(1/(A : ℝ)) ≤ (L+H+b+1)*((1+T)/(A : ℝ)) := by
    have h1 : 1/(A : ℝ) ≤ (1+T)/(A : ℝ) := div_le_div_of_nonneg_right (by linarith) hAr.le
    have h2 : T1/(A : ℝ) ≤ (1+T)/(A : ℝ) := div_le_div_of_nonneg_right hT1upper hAr.le
    have hL' := mul_le_mul_of_nonneg_left h1 hL
    have hH' := mul_le_mul_of_nonneg_left h2 hH
    have hb' := mul_le_mul_of_nonneg_left h1 hb0
    rw [mul_one_div] at hL'
    nlinarith
  have htri : |logDistinctTrace68 p k A B-b*T+cycleRangeMass68 p k| ≤
      |logDistinctTrace68 p k A B-logGridTrace68 p k A B|+
      |logGridTrace68 p k A B-relativeIdealTrace68 p k T1|+
      |relativeIdealTrace68 p k T1-b*T1+cycleRangeMass68 p k|+|b*d| := by
    have hid : logDistinctTrace68 p k A B-b*T+cycleRangeMass68 p k =
        ((logDistinctTrace68 p k A B-logGridTrace68 p k A B)+
        (logGridTrace68 p k A B-relativeIdealTrace68 p k T1))+
        (relativeIdealTrace68 p k T1-b*T1+cycleRangeMass68 p k)+b*d := by rw [hT1]; ring
    rw [hid]
    have h1 := abs_add_le (logDistinctTrace68 p k A B-logGridTrace68 p k A B)
      (logGridTrace68 p k A B-relativeIdealTrace68 p k T1)
    have h2 := abs_add_le ((logDistinctTrace68 p k A B-logGridTrace68 p k A B)+
      (logGridTrace68 p k A B-relativeIdealTrace68 p k T1))
      (relativeIdealTrace68 p k T1-b*T1+cycleRangeMass68 p k)
    have h3 := abs_add_le (((logDistinctTrace68 p k A B-logGridTrace68 p k A B)+
      (logGridTrace68 p k A B-relativeIdealTrace68 p k T1))+
      (relativeIdealTrace68 p k T1-b*T1+cycleRangeMass68 p k)) (b*d)
    linarith
  change |logDistinctTrace68 p k A B-b*T+cycleRangeMass68 p k| ≤ _
  dsimp only [L] at hrem
  dsimp only [H,T1] at hrem
  linarith

end Luce.Section6
