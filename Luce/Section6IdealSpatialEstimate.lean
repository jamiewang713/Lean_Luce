import Luce.Section6IdealTraceTotal
import Luce.Section6IdealTraceRestriction
import Luce.Section6IdealSpatialWindow

noncomputable section
namespace Luce.Section6

theorem idealTrace_refined68 (side : Corner) (behavior : EndpointBehavior)
    (hactive : behavior.active) (hg : 0 < localCornerExponent behavior)
    (hq : 0 < localCornerQ side behavior) (k : ℕ) :
    ∃ E D c d : ℝ, 0 < E ∧ 0 < D ∧ 0 < c ∧ ∀ A B : ℕ, 1 ≤ A → A ≤ B →
      |idealTrace side behavior k A B-cornerCoefficient side behavior k*Real.log ((B : ℝ)/A)+d| ≤
        E*((1+Real.log ((B : ℝ)/A))/(A : ℝ))+D*Real.exp (-c*Real.log ((B : ℝ)/A)) := by
  have hp := cornerLogDensity68_traceDensity side behavior hg hq
  obtain ⟨C,hC,hb⟩ := cornerLogDensity68_smooth_envelope side behavior hg hq
  obtain ⟨E,D,c,hE,hD,hc,h⟩ := logDistinctTrace68_refined hp
    (cornerLogDensity68_differentiable side behavior) hC hg hb k
  refine ⟨E,D,c,cycleRangeMass68 (cornerLogDensity68 side behavior) k,hE,hD,hc,?_⟩
  intro A B hA hAB
  rw [idealTrace_eq_logDistinct68 side behavior k hA,
    cornerCoefficient_logDensity68 side behavior hactive k]
  exact h A B hA hAB

theorem refined_interval_core_bound68 {I : ℕ → ℕ → ℝ} {β E D c d : ℝ}
    (hE : 0 ≤ E) (hD : 0 ≤ D)
    (htrace : ∀ A B : ℕ, 1 ≤ A → A ≤ B →
      |I A B-β*Real.log ((B : ℝ)/A)+d| ≤
        E*((1+Real.log ((B : ℝ)/A))/(A : ℝ))+D*Real.exp (-c*Real.log ((B : ℝ)/A)))
    {A n P Q : ℕ} (hA : 1 ≤ A) (hAP : A ≤ P) (hPQ : P ≤ Q) (hQn : Q ≤ n)
    (hgap : Real.log (A : ℝ) ≤ c*Real.log ((Q : ℝ)/P)) :
    |I P Q-β*Real.log ((Q : ℝ)/P)+d| ≤ (E+D)*((1+Real.log (n : ℝ))/(A : ℝ)) := by
  have hP : 1 ≤ P := hA.trans hAP
  have hQ : 1 ≤ Q := hP.trans hPQ
  have hn : 1 ≤ n := hQ.trans hQn
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hT : 0 ≤ Real.log ((Q : ℝ)/P) := Real.log_nonneg ((one_le_div hP0).mpr (by exact_mod_cast hPQ))
  have hTn : Real.log ((Q : ℝ)/P) ≤ Real.log (n : ℝ) := by
    rw [Real.log_div hQ0.ne' hP0.ne']
    have h := monotone_nat_log68 hQn
    have := Real.log_natCast_nonneg P
    linarith
  have hnlog := Real.log_natCast_nonneg n
  have hfrac : (1+Real.log ((Q : ℝ)/P))/(P : ℝ) ≤ (1+Real.log (n : ℝ))/(A : ℝ) :=
    (div_le_div_of_nonneg_right (by linarith) hP0.le).trans
      (div_le_div_of_nonneg_left (by positivity) hA0 (by exact_mod_cast hAP))
  have hexp : Real.exp (-c*Real.log ((Q : ℝ)/P)) ≤ 1/(A : ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log (A : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1/(A : ℝ) := by rw [Real.exp_neg, Real.exp_log hA0, one_div]
  have h1 : 1/(A : ℝ) ≤ (1+Real.log (n : ℝ))/(A : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hA0.le
  have h := htrace P Q hP hPQ
  have hEf := mul_le_mul_of_nonneg_left hfrac hE
  have hDf := mul_le_mul_of_nonneg_left (hexp.trans h1) hD
  nlinarith

theorem trace_subtraction_error68 {I₁ I₂ T₁ T₂ β d H : ℝ}
    (h₁ : |I₁-β*T₁+d| ≤ H) (h₂ : |I₂-β*T₂+d| ≤ H) :
    |I₁-I₂-β*(T₁-T₂)| ≤ 2*H := by
  have h := abs_sub_le (I₁-β*T₁+d) 0 (I₂-β*T₂+d)
  simp only [sub_zero, zero_sub, abs_neg] at h
  have hid : I₁-I₂-β*(T₁-T₂) = (I₁-β*T₁+d)-(I₂-β*T₂+d) := by ring
  rw [hid]
  linarith

theorem idealSpatialTrace68_window_bound (side : Corner) (behavior : EndpointBehavior)
    (k : ℕ) {E D c d a b : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D) (hc : 0 ≤ c)
    (htrace : ∀ A B : ℕ, 1 ≤ A → A ≤ B →
      |idealTrace side behavior k A B-cornerCoefficient side behavior k*Real.log ((B : ℝ)/A)+d| ≤
        E*((1+Real.log ((B : ℝ)/A))/(A : ℝ))+D*Real.exp (-c*Real.log ((B : ℝ)/A)))
    {n : ℕ} (hw : IdealSpatialWindow68 n a b c) :
    |idealSpatialTrace side behavior k n a b-cornerCoefficient side behavior k*(b-a)*Real.log (n : ℝ)| ≤
      (2*(E+D)+2*|cornerCoefficient side behavior k|)*((1+Real.log (n : ℝ))/(idealCoreLower n : ℝ)) := by
  let A := idealCoreLower n
  let B := idealCoreUpper n
  let P := ⌊(n : ℝ)^a⌋₊
  let Q := ⌊(n : ℝ)^b⌋₊
  let β := cornerCoefficient side behavior k
  let L := Real.log (n : ℝ)
  have hA : 1 ≤ A := idealCoreLower_pos68 n
  have hAP : A ≤ P := hw.lower_le
  have hPQ : P ≤ Q := hw.threshold_le
  have hQB : Q+1 ≤ B := hw.upper_le
  have hBn : B ≤ n := hw.core_le_n
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hP10 : (0 : ℝ) < (P+1 : ℕ) := by positivity
  have hQ10 : (0 : ℝ) < (Q+1 : ℕ) := by positivity
  have hL : 0 ≤ L := Real.log_natCast_nonneg n
  have hf : 1/(A : ℝ) ≤ (1+L)/(A : ℝ) := div_le_div_of_nonneg_right (by linarith) hA0.le
  have hfinal {X T : ℝ} (hX : |X-β*T| ≤ 2*((E+D)*((1+L)/(A : ℝ))))
      (hT : |T-(b-a)*L| ≤ 2/(A : ℝ)) :
      |X-β*(b-a)*L| ≤ (2*(E+D)+2*|β|)*((1+L)/(A : ℝ)) := by
    have hmul : |β*(T-(b-a)*L)| ≤ |β| *(2/(A : ℝ)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hT (abs_nonneg β)
    have htri := abs_add_le (X-β*T) (β*(T-(b-a)*L))
    have hid : X-β*T+β*(T-(b-a)*L) = X-β*(b-a)*L := by ring
    rw [hid] at htri
    have hβ := mul_le_mul_of_nonneg_left hf (abs_nonneg β)
    have hβ' : |β| *(2/(A : ℝ)) ≤ 2*|β| *((1+L)/(A : ℝ)) := by
      calc
        _ = 2*(|β| *(1/(A : ℝ))) := by ring
        _ ≤ 2*(|β| *((1+L)/(A : ℝ))) := mul_le_mul_of_nonneg_left hβ (by norm_num)
        _ = _ := by ring
    exact htri.trans ((add_le_add hX (hmul.trans hβ')).trans_eq (by ring))
  unfold idealSpatialTrace
  rw [idealRootTrace_floor68 side behavior k A B (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  cases side
  · rw [idealRootTrace_left_sub68 behavior k hPQ (show Q ≤ B by omega)]
    have hgapP := hw.left_gap
    have hgapQ : Real.log (A : ℝ) ≤ c*Real.log ((Q : ℝ)/A) := by
      apply hgapP.trans
      apply mul_le_mul_of_nonneg_left _ hc
      rw [Real.log_div hQ0.ne' hA0.ne', Real.log_div hP0.ne' hA0.ne']
      exact sub_le_sub_right (monotone_nat_log68 hPQ) _
    have h₁ := refined_interval_core_bound68 hE hD htrace hA le_rfl
      (hAP.trans hPQ) ((show Q ≤ B by omega).trans hBn) hgapQ
    have h₂ := refined_interval_core_bound68 hE hD htrace hA le_rfl hAP
      (hPQ.trans ((show Q ≤ B by omega).trans hBn)) hgapP
    apply hfinal (trace_subtraction_error68 h₁ h₂)
    rw [Real.log_div hQ0.ne' hA0.ne', Real.log_div hP0.ne' hA0.ne']
    have h := abs_sub_le (Real.log (Q : ℝ)-b*L) 0 (Real.log (P : ℝ)-a*L)
    simp only [sub_zero, zero_sub, abs_neg] at h
    have hid : Real.log (Q : ℝ)-Real.log (A : ℝ)-(Real.log (P : ℝ)-Real.log (A : ℝ))-(b-a)*L =
        (Real.log (Q : ℝ)-b*L)-(Real.log (P : ℝ)-a*L) := by ring
    rw [hid]
    exact h.trans ((add_le_add hw.floor_b_error hw.floor_a_error).trans_eq (by ring))
  · rw [idealRootTrace_right_sub68 behavior k (show A ≤ P+1 by omega) hPQ]
    have hgapQ := hw.right_gap
    have hgapP : Real.log (A : ℝ) ≤ c*Real.log ((B : ℝ)/(P+1 : ℕ)) := by
      apply hgapQ.trans
      apply mul_le_mul_of_nonneg_left _ hc
      rw [Real.log_div hB0.ne' hP10.ne', Real.log_div hB0.ne' hQ10.ne']
      exact sub_le_sub_left (monotone_nat_log68 (Nat.add_le_add_right hPQ 1)) _
    have h₁ := refined_interval_core_bound68 hE hD htrace hA (show A ≤ P+1 by omega)
      (show P+1 ≤ B by omega) hBn hgapP
    have h₂ := refined_interval_core_bound68 hE hD htrace hA (show A ≤ Q+1 by omega) hQB hBn hgapQ
    apply hfinal (trace_subtraction_error68 h₁ h₂)
    rw [Real.log_div hB0.ne' hP10.ne', Real.log_div hB0.ne' hQ10.ne']
    have h := abs_sub_le (Real.log ((Q+1 : ℕ) : ℝ)-b*L) 0 (Real.log ((P+1 : ℕ) : ℝ)-a*L)
    simp only [sub_zero, zero_sub, abs_neg] at h
    have hid : Real.log (B : ℝ)-Real.log ((P+1 : ℕ) : ℝ)-
        (Real.log (B : ℝ)-Real.log ((Q+1 : ℕ) : ℝ))-(b-a)*L =
        (Real.log ((Q+1 : ℕ) : ℝ)-b*L)-(Real.log ((P+1 : ℕ) : ℝ)-a*L) := by ring
    rw [hid]
    exact h.trans ((add_le_add hw.succ_b_error hw.succ_a_error).trans_eq (by ring))

end Luce.Section6
