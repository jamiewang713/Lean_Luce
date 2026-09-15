import Luce.ExponentialFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Exponential memorylessness as an equality of measures -/

open MeasureTheory ProbabilityTheory Set

namespace Luce

/-- After survival to a deterministic time `s`, subtracting `s` from an
exponential clock leaves the original exponential law, multiplied by the
survival probability. This unnormalized identity avoids conditioning on a
zero-probability exact clock value. -/
theorem exponential_residual_measure {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    ((expMeasure r).restrict (Ioi s)).map (fun x => x - s) =
      ENNReal.ofReal (Real.exp (-(r * s))) • expMeasure r := by
  letI := isProbabilityMeasure_expMeasure hr
  have hf : Measurable (fun x : ℝ => x - s) := measurable_id.sub_const s
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hf measurableSet_Iic,
    Measure.restrict_apply (hf measurableSet_Iic),
    Measure.smul_apply, smul_eq_mul]
  by_cases ht : 0 ≤ t
  · have he : (fun x : ℝ => x - s) ⁻¹' Iic t ∩ Ioi s = Ioc s (s + t) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioi, Set.mem_Ioc]
      constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
    have hIoc : expMeasure r (Ioc s (s + t)) =
        ENNReal.ofReal (cdf (expMeasure r) (s + t) - cdf (expMeasure r) s) := by
      calc
        _ = (cdf (expMeasure r)).measure (Ioc s (s + t)) := by rw [measure_cdf]
        _ = _ := (cdf (expMeasure r)).measure_Ioc _ _
    rw [he, hIoc, ← ofReal_cdf, cdf_expMeasure_eq hr, cdf_expMeasure_eq hr,
      cdf_expMeasure_eq hr, if_pos (add_nonneg hs ht), if_pos hs, if_pos ht,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    have hexp : -(r * (s + t)) = -(r * s) + -(r * t) := by ring
    rw [hexp, Real.exp_add]
    ring
  · have he : (fun x : ℝ => x - s) ⁻¹' Iic t ∩ Ioi s = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioi,
        Set.mem_empty_iff_false, iff_false]
      intro hx
      linarith [hx.1, hx.2]
    rw [he, measure_empty, ← ofReal_cdf, cdf_expMeasure_eq hr, if_neg ht]
    simp

end Luce

