import Luce.Section6InsertionSecondMoment
import Luce.Section6LocalErrorPowers

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Luce.Section6

/-- Joint normalized-gap estimate assembled from genuine one-edge events
and one-edge moments. All dependence on the shared background is retained. -/
theorem joint_normalized_estimate {n s r : ℕ} (w : Weights n) (hs0 : 0 < s) (hsr : s ≤ r)
    (removed : Finset (Fin n)) (u : Fin s → Fin n)
    (q : Fin s ↪ Fin (Finset.univ \ removed).card)
    (K H E m : Fin s → ℝ) (hK : ∀ i, 0 ≤ K i) (hH : ∀ i, 0 ≤ H i)
    (hE : ∀ i, 0 ≤ E i) (hm : ∀ i, 0 < m i)
    {C J : ℝ} (hC : 1 ≤ C) (hJ : 0 ≤ J)
    (hKB : ∀ i, K i ≤ C*H i)
    (hquarter : ∀ i, (m i)^(-(1/4 : ℝ)) ≤ E i) (hinv : ∀ i, 1/m i ≤ E i)
    (hlp : ∀ i, eLpNorm (fun old => (deletedGapKernel w removed old (u i) (q i).val).toReal)
      ((2*s : ℕ) : ℝ≥0∞) (exponentialRace w) ≤ ENNReal.ofReal (C*H i))
    (hcontrol : ∀ i, ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
      (exponentialRace w).real Gᶜ ≤ J*(m i)^(-(1/2 : ℝ)) ∧
      ∀ᵐ old ∂exponentialRace w, old ∈ G →
        (deletedGapKernel w removed old (u i) (q i).val).toReal ≤ C*H i*markedNormalizedGaps w removed q old i ∧
        |(deletedGapKernel w removed old (u i) (q i).val).toReal-K i*markedNormalizedGaps w removed q old i| ≤
          C*H i*((2*E i)*markedNormalizedGaps w removed q old i+
            (markedNormalizedGaps w removed q old i)^2/m i)) :
    |(∫ old, ∏ i, (deletedGapKernel w removed old (u i) (q i).val).toReal ∂exponentialRace w)-
        (∏ i, K i)| ≤
      (C^r*(4+(1+Real.sqrt ((2 : ℝ)^r))*Real.sqrt J))*(∏ i, H i)*(∑ i, E i) := by
  classical
  choose G hG hprob hpoint using hcontrol
  let good := ⋂ i, G i
  have hgood : MeasurableSet good := MeasurableSet.iInter hG
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hB : ∀ i, 0 ≤ C*H i := fun i => mul_nonneg hC0 (hH i)
  have hP : (exponentialRace w).real goodᶜ ≤ J*(∑ i, (m i)^(-(1/2 : ℝ))) := by
    dsimp only [good]
    rw [compl_iInter]
    apply (measureReal_iUnion_fintype_le _).trans
    calc
      _ ≤ ∑ i, J*(m i)^(-(1/2 : ℝ)) := Finset.sum_le_sum (fun i _ => hprob i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hpoint' : ∀ᵐ old ∂exponentialRace w, old ∈ good → ∀ i,
      (deletedGapKernel w removed old (u i) (q i).val).toReal ≤
        (C*H i)*markedNormalizedGaps w removed q old i ∧
      |(deletedGapKernel w removed old (u i) (q i).val).toReal-K i*markedNormalizedGaps w removed q old i| ≤
        (C*H i)*((2*E i)*markedNormalizedGaps w removed q old i+
          (1/m i)*(markedNormalizedGaps w removed q old i)^2) := by
    filter_upwards [ae_all_iff.mpr hpoint] with old hold
    intro hg i
    have hi := hold i (mem_iInter.mp hg i)
    exact ⟨hi.1, hi.2.trans_eq (by ring)⟩
  have hBprod : 0 ≤ ∏ i, C*H i := Finset.prod_nonneg (fun i _ => hB i)
  have hKprod : 0 ≤ ∏ i, K i := Finset.prod_nonneg (fun i _ => hK i)
  have hEtotal : 0 ≤ ∑ i, E i := Finset.sum_nonneg (fun i _ => hE i)
  have hHprod : 0 ≤ ∏ i, H i := Finset.prod_nonneg (fun i _ => hH i)
  have hsecond := deleted_kernel_product_second_moment_bound w hs0 removed u
    (fun i => (q i).val) (fun i => C*H i) hB hlp
  have herr := actual_normalized_product_error w removed u q K (fun i => C*H i)
    (fun i => 2*E i) (fun i => 1/m i) hK hB (fun i => mul_nonneg (by norm_num) (hE i))
    (fun i => one_div_nonneg.mpr (hm i).le) hKB hgood hpoint' hBprod hsecond
  have hsqrt : Real.sqrt ((exponentialRace w).real goodᶜ) ≤ Real.sqrt J*(∑ i, E i) := by
    apply (Real.sqrt_le_sqrt hP).trans
    rw [Real.sqrt_mul hJ]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    calc
      _ ≤ ∑ i, Real.sqrt ((m i)^(-(1/2 : ℝ))) :=
        sqrt_sum_le_sum_sqrt _ (fun i => Real.rpow_nonneg (hm i).le _)
      _ = ∑ i, (m i)^(-(1/4 : ℝ)) := by simp_rw [quarter_window_square_root (hm _)]
      _ ≤ ∑ i, E i := Finset.sum_le_sum (fun i _ => hquarter i)
  have hsum : (∑ i, (2*E i+2*(1/m i))) ≤ 4*(∑ i, E i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    linarith only [hinv i]
  have hprod : (∏ i, K i) ≤ ∏ i, C*H i := Finset.prod_le_prod (fun i _ => hK i) (fun i _ => hKB i)
  have htwo : Real.sqrt ((2 : ℝ)^s) ≤ Real.sqrt ((2 : ℝ)^r) :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hsr)
  have hprodbound : (∏ i, C*H i) ≤ C^r*(∏ i, H i) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hsr) hHprod
  calc
    _ ≤ (∏ i, C*H i)*(4*(∑ i, E i))+
        ((∏ i, C*H i)+(∏ i, C*H i)*Real.sqrt ((2 : ℝ)^r))*(Real.sqrt J*(∑ i, E i)) := by
      apply herr.trans
      apply add_le_add (mul_le_mul_of_nonneg_left hsum hBprod)
      apply mul_le_mul _ hsqrt (Real.sqrt_nonneg _)
        (add_nonneg hBprod (mul_nonneg hBprod (Real.sqrt_nonneg _)))
      exact add_le_add le_rfl (mul_le_mul hprod htwo (Real.sqrt_nonneg _) hBprod)
    _ = (∏ i, C*H i)*(4+(1+Real.sqrt ((2 : ℝ)^r))*Real.sqrt J)*(∑ i, E i) := by ring
    _ ≤ (C^r*(∏ i, H i))*(4+(1+Real.sqrt ((2 : ℝ)^r))*Real.sqrt J)*(∑ i, E i) := by
      apply mul_le_mul_of_nonneg_right _ hEtotal
      exact mul_le_mul_of_nonneg_right hprodbound (by positivity)
    _ = _ := by ring

end Luce.Section6
