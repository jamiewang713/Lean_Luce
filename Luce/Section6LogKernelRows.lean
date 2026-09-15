import Luce.Section6CyclePerturbation

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce.Section6

def logKernel68 (p : ℝ → ℝ) (a b : ℕ) : ℝ := p (Real.log (a : ℝ)-Real.log (b : ℝ))/(b : ℝ)

theorem log_kernel_row68 {p : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x) {C g : ℝ}
    (hC : 0 ≤ C) (hg : 0 < g) (hb : ∀ x, p x ≤ C*Real.exp (-g*|x|))
    {A B : ℕ} (hA : 1 ≤ A) (s : ℝ) :
    (∑ m : ↥(Finset.Icc A B), p (s-Real.log (m.val : ℝ))/(m.val : ℝ)) ≤
      (2*C*Real.exp g)*(2/g) := by
  let f : ℝ → ℝ := fun x => Real.exp (-g*|s-x|)
  have hf : Integrable f := (integrable_exp_neg_abs68 hg).comp_sub_left s
  have he : (∫ x : ℝ, f x) = 2/g := by
    rw [integral_sub_left_eq_self (fun x : ℝ => Real.exp (-g*|x|)) volume s, integral_exp_neg_abs68 hg]
  have hcell (m : ↥(Finset.Icc A B)) :
      p (s-Real.log (m.val : ℝ))/(m.val : ℝ) ≤ (2*C*Real.exp g)*(∫ x in logCell68 m.val, f x) := by
    have hm : 0 < m.val := by have := (Finset.mem_Icc.mp m.property).1; omega
    have hmR : 0 < (m.val : ℝ) := by exact_mod_cast hm
    have hw := logCellWidth68_pos hm
    have hcorr := logCellCorrection68_bounds (A := 1) (by omega) (by omega : 1 ≤ m.val)
    norm_num at hcorr
    have hi : IntegrableOn (fun _ : ℝ => logCellCorrection68 m.val*p (s-Real.log (m.val : ℝ)))
        (logCell68 m.val) := by unfold logCell68; exact integrable_const _
    have hid : (∫ _x in logCell68 m.val, logCellCorrection68 m.val*p (s-Real.log (m.val : ℝ))) =
        p (s-Real.log (m.val : ℝ))/(m.val : ℝ) := by
      rw [setIntegral_const, smul_eq_mul]
      have hv : volume.real (logCell68 m.val) = logCellWidth68 m.val := by
        unfold logCell68 logCellWidth68
        rw [Real.volume_real_Ioc_of_le (monotone_nat_log68 (Nat.le_succ _))]
      rw [hv]
      unfold logCellCorrection68
      field_simp
    rw [← hid, ← integral_const_mul]
    apply integral_mono_ae hi (hf.integrableOn.const_mul _)
    filter_upwards [ae_restrict_mem (show MeasurableSet (logCell68 m.val) from measurableSet_Ioc)] with x hx
    have hx' : |(s-Real.log (m.val : ℝ))-(s-x)| ≤ 1 := by
      have hh := logCell68_offset (A := 1) (by omega) (by omega : 1 ≤ m.val) hx
      norm_num at hh
      convert hh using 1 <;> first | rfl | (congr 1; ring)
    have hshift := exp_abs_shift_bound68 hg.le hx'
    simp only [mul_one] at hshift
    have hpb : p (s-Real.log (m.val : ℝ)) ≤ C*Real.exp g*f x :=
      (hb _).trans ((mul_le_mul_of_nonneg_left hshift hC).trans_eq (by dsimp [f]; ring))
    calc
      _ ≤ 2*(C*Real.exp g*f x) := mul_le_mul hcorr.2 hpb (hp _) (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ∑ m : ↥(Finset.Icc A B), (2*C*Real.exp g)*(∫ x in logCell68 m.val, f x) :=
      Finset.sum_le_sum (fun m _ => hcell m)
    _ = (2*C*Real.exp g)*(∫ x in Ioc (Real.log (A : ℝ)) (Real.log ((B+1 : ℕ) : ℝ)), f x) := by
      rw [← Finset.mul_sum]
      congr 1
      have hh := integral_iUnion_fintype (fun m : ↥(Finset.Icc A B) =>
        (show MeasurableSet (logCell68 m.val) from measurableSet_Ioc))
        (fun m n hmn => logCell68_disjoint (fun h => hmn (Subtype.ext h)))
        (fun _ => hf.integrableOn)
      rw [logCell68_union] at hh
      exact hh.symm
    _ ≤ (2*C*Real.exp g)*(∫ x : ℝ, f x) := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hf (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))) (by positivity)
    _ = _ := by rw [he]

theorem log_kernel_target68 {p : ℝ → ℝ} {C g : ℝ} (hC : 0 ≤ C) (hg : 0 ≤ g)
    (hb : ∀ x, p x ≤ C*Real.exp (-g*|x|)) (a b : ℕ) :
    logKernel68 p a b ≤ C*(1/(b : ℝ)) := by
  unfold logKernel68
  have h : p (Real.log (a : ℝ)-Real.log (b : ℝ)) ≤ C := (hb _).trans
    (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg) (abs_nonneg _))))
  simpa only [div_eq_mul_inv, one_mul] using div_le_div_of_nonneg_right h (Nat.cast_nonneg b)

end Luce.Section6
