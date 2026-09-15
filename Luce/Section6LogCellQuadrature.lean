import Luce.Section6CyclePerturbation
import Luce.Section6ContinuousBoxTrace

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce.Section6

def logGridErrorConstant68 (C g : ℝ) (k : ℕ) : ℝ :=
  3*((k : ℝ)+1)*(2 : ℝ)^(k+1)*(C*Real.exp (2*g))^(k+1)

theorem logCellCube68_integrable {A B k : ℕ} (a : IdealDepthTuple A B k)
    {f : (Fin (k+1) → ℝ) → ℝ} (hf : Continuous f) : IntegrableOn f (logCellCube68 a) := by
  apply hf.integrableOn_Icc.mono_set
    (t := Icc (fun j => Real.log ((a j).val : ℝ)) (fun j => Real.log (((a j).val+1 : ℕ) : ℝ)))
  intro x hx
  constructor <;> intro j
  · exact ((hx j (mem_univ j)).1).le
  · exact (hx j (mem_univ j)).2

theorem logCellCube68_constant_identity {A B k : ℕ} (hA : 1 ≤ A)
    (a : IdealDepthTuple A B k) (v : ℝ) :
    (∫ _x in logCellCube68 a, (∏ j, logCellCorrection68 (a j).val)*v) =
      v*(∏ j, 1/((a j).val : ℝ)) := by
  rw [setIntegral_const, smul_eq_mul, logCellCube68_volume hA]
  have hp : (∏ j, logCellWidth68 (a j).val)*(∏ j, logCellCorrection68 (a j).val) =
      ∏ j, 1/((a j).val : ℝ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    have hm : 0 < (a j).val := by have := (Finset.mem_Icc.mp (a j).property).1; omega
    have hw := logCellWidth68_pos hm
    unfold logCellCorrection68
    field_simp
  rw [← mul_assoc, hp, mul_comm]

theorem logCellCube68_pointwise_error {p : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hd : Differentiable ℝ p) {C g : ℝ} (hC : 0 ≤ C) (hg : 0 ≤ g)
    (hb : ∀ x, p x+‖deriv p x‖ ≤ C*Real.exp (-g*|x|))
    {A B k : ℕ} (hA : 1 ≤ A) (a : IdealDepthTuple A B k)
    {x : Fin (k+1) → ℝ} (hx : x ∈ logCellCube68 a) :
    |(∏ j, logCellCorrection68 (a j).val)*
      closedLogCycleWeight p k (fun j => Real.log ((a j).val : ℝ))-closedLogCycleWeight p k x| ≤
      (logGridErrorConstant68 C g k/(A : ℝ))*
        closedLogCycleWeight (fun t => Real.exp (-g*|t|)) k x := by
  let e : ℝ := 1/(A : ℝ)
  let R : ℝ := ∏ j, logCellCorrection68 (a j).val
  let P := closedLogCycleWeight p k (fun j => Real.log ((a j).val : ℝ))
  let Q := closedLogCycleWeight p k x
  let V := closedLogCycleWeight (fun t => Real.exp (-g*|t|)) k x
  let D := (C*Real.exp (2*g))^(k+1)*V
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by
    dsimp [e]
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by exact_mod_cast hA)).trans_eq (by norm_num)
  have hax (j : Fin (k+1)) : |Real.log ((a j).val : ℝ)-x j| ≤ e := by
    rw [abs_sub_comm]
    exact logCell68_offset hA (Finset.mem_Icc.mp (a j).property).1 (hx j (mem_univ j))
  have hc := closed_cycle_perturbation68 hp hd hC hg he0 he1 hb k
    (fun j => Real.log ((a j).val : ℝ)) x hax
  have hPQ : |P-Q| ≤ 2*((k : ℝ)+1)*e*D := by
    convert hc.1 using 1 <;> first | rfl | (dsimp [D]; ring)
  have hQ : Q ≤ D := hc.2
  have hQ0 : 0 ≤ Q := closedLogCycleWeight_nonneg68 hp _ _
  have hD0 : 0 ≤ D := hQ0.trans hQ
  have hR := logCellCorrection68_product_bounds hA a
  change 0 ≤ R ∧ R ≤ (2 : ℝ)^(k+1) ∧ |R-1| ≤ ((k : ℝ)+1)*e*(2 : ℝ)^(k+1) at hR
  change |R*P-Q| ≤ (logGridErrorConstant68 C g k/(A : ℝ))*V
  calc
    _ = |R*(P-Q)+(R-1)*Q| := by congr 1; ring
    _ ≤ R * |P-Q| + |R-1| * Q := by
      simpa only [abs_mul, abs_of_nonneg hR.1, abs_of_nonneg hQ0] using abs_add_le (R*(P-Q)) ((R-1)*Q)
    _ ≤ (2 : ℝ)^(k+1)*(2*((k : ℝ)+1)*e*D)+(((k : ℝ)+1)*e*(2 : ℝ)^(k+1))*D := by
      apply add_le_add
      · exact mul_le_mul hR.2.1 hPQ (abs_nonneg _) (by positivity)
      · exact mul_le_mul hR.2.2 hQ hQ0 (by positivity)
    _ = _ := by dsimp [logGridErrorConstant68, e, D]; ring

theorem logCellCube68_integral_error {p : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hd : Differentiable ℝ p) {C g : ℝ} (hC : 0 ≤ C) (hg : 0 ≤ g)
    (hb : ∀ x, p x+‖deriv p x‖ ≤ C*Real.exp (-g*|x|))
    {A B k : ℕ} (hA : 1 ≤ A) (a : IdealDepthTuple A B k) :
    |closedLogCycleWeight p k (fun j => Real.log ((a j).val : ℝ))*(∏ j, 1/((a j).val : ℝ))-
      ∫ x in logCellCube68 a, closedLogCycleWeight p k x| ≤
      (logGridErrorConstant68 C g k/(A : ℝ))*
        ∫ x in logCellCube68 a, closedLogCycleWeight (fun t => Real.exp (-g*|t|)) k x := by
  have hpI := logCellCube68_integrable a (closedLogCycleWeight_continuous68 hd.continuous k)
  have heC : Continuous (closedLogCycleWeight (fun t => Real.exp (-g*|t|)) k) :=
    closedLogCycleWeight_continuous68 (by fun_prop) k
  have heI := logCellCube68_integrable a heC
  have hconst := logCellCube68_integrable a (continuous_const (y :=
    (∏ j, logCellCorrection68 (a j).val)*closedLogCycleWeight p k (fun j => Real.log ((a j).val : ℝ))))
  rw [← logCellCube68_constant_identity hA a, ← integral_sub hconst hpI, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_ae (hconst.sub hpI).norm (heI.const_mul _)
  filter_upwards [ae_restrict_mem (logCellCube68_measurable a)] with x hx
  exact logCellCube68_pointwise_error hp hd hC hg hb hA a hx

end Luce.Section6
