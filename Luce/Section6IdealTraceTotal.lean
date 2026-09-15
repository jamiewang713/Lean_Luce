import Luce.Section6IdealTraceAsymptotic
import Luce.Section6IdealLogKernel
import Luce.Section6Lemma68Contract
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem cornerLogDensity68_differentiable (side : Corner) (behavior : EndpointBehavior) :
    Differentiable ℝ (cornerLogDensity68 side behavior) := by
  cases side <;> unfold cornerLogDensity68 incrementDensity <;> fun_prop

theorem cornerLogDensity68_smooth_envelope (side : Corner) (behavior : EndpointBehavior)
    (hg : 0 < localCornerExponent behavior) (hq : 0 < localCornerQ side behavior) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, cornerLogDensity68 side behavior x+
      ‖deriv (cornerLogDensity68 side behavior) x‖ ≤ C*Real.exp (-localCornerExponent behavior*|x|) := by
  obtain ⟨C,hC,hb⟩ := incrementDensity_exponential_envelope hg hq
  refine ⟨C,hC,?_⟩
  intro x
  cases side
  · change incrementDensity (localCornerExponent behavior) (localCornerQ .left behavior) (-x)+
      ‖deriv (fun t => incrementDensity (localCornerExponent behavior) (localCornerQ .left behavior) (-t)) x‖ ≤ _
    rw [deriv_comp_neg, norm_neg]
    simpa only [abs_neg] using hb (-x)
  · exact hb x

theorem idealTrace_eq_logDistinct68 (side : Corner) (behavior : EndpointBehavior)
    (k : ℕ) {A B : ℕ} (hA : 1 ≤ A) :
    idealTrace side behavior k A B = logDistinctTrace68 (cornerLogDensity68 side behavior) k A B := by
  classical
  have hinj (a : IdealDepthTuple A B k) :
      Function.Injective (fun j => (a j).val) ↔ Function.Injective a := by
    constructor
    · intro h i j hij
      exact h (congrArg Subtype.val hij)
    · intro h
      exact Subtype.val_injective.comp h
  unfold idealTrace logDistinctTrace68
  simp_rw [hinj]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  unfold idealCycleWeight collisionCycleWeight
  apply Finset.prod_congr rfl
  intro j _
  exact localIdealKernel_log68 side behavior
    (lt_of_lt_of_le Nat.zero_lt_one (hA.trans (Finset.mem_Icc.mp (a j).property).1))
    (lt_of_lt_of_le Nat.zero_lt_one (hA.trans (Finset.mem_Icc.mp (a (finRotate (k+1) j)).property).1))

theorem lemma68_total : Lemma68Contract.total := by
  intro f left right hp side hactive k
  let behavior := cornerBehavior left right side
  obtain ⟨hg,hq⟩ := hp.local_corner_parameters_pos side hactive
  have hpD := cornerLogDensity68_traceDensity side behavior hg hq
  obtain ⟨C,hC,hbound⟩ := cornerLogDensity68_smooth_envelope side behavior hg hq
  obtain ⟨E,D,c,hE,hD,hc,htrace⟩ := logDistinctTrace68_refined hpD
    (cornerLogDensity68_differentiable side behavior) hC hg hbound k
  let d := cycleRangeMass68 (cornerLogDensity68 side behavior) k
  refine ⟨|d|+D+1,E,by positivity,hE,1,by omega,?_⟩
  intro A B hA hAB
  rw [idealTrace_eq_logDistinct68 side behavior k hA,
    cornerCoefficient_logDensity68 side behavior hactive k]
  have h := htrace A B hA hAB
  have hA0 : 0 < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hT : 0 ≤ Real.log ((B : ℝ)/A) :=
    Real.log_nonneg ((one_le_div hA0).mpr (by exact_mod_cast hAB))
  have he : D*Real.exp (-c*Real.log ((B : ℝ)/A)) ≤ D :=
    mul_le_of_le_one_right hD.le (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hT))
  have ht := abs_sub_le
    (logDistinctTrace68 (cornerLogDensity68 side behavior) k A B-
      (traceConvolution68 (cornerLogDensity68 side behavior) k 0/((k : ℝ)+1))*Real.log ((B : ℝ)/A)+d)
    0 d
  simp only [sub_zero, zero_sub, abs_neg, add_sub_cancel_right] at ht
  change |logDistinctTrace68 (cornerLogDensity68 side behavior) k A B-
    (traceConvolution68 (cornerLogDensity68 side behavior) k 0/((k : ℝ)+1))*Real.log ((B : ℝ)/A)| ≤ _
  linarith

end Luce.Section6
