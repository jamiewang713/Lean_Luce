import Luce.Section6LogCells
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce.Section6

theorem exp_abs_shift_bound68 {g d u v : ℝ} (hg : 0 ≤ g) (huv : |u-v| ≤ d) :
    Real.exp (-g*|u|) ≤ Real.exp (g*d)*Real.exp (-g*|v|) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht := abs_sub_le v u 0
  rw [sub_zero, sub_zero, abs_sub_comm v u] at ht
  nlinarith

/-- A local perturbation retains an integrable exponential envelope. -/
theorem density_perturbation68 {p : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hd : Differentiable ℝ p) {C g e u v : ℝ}
    (hC : 0 ≤ C) (hg : 0 ≤ g) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hb : ∀ x, p x+‖deriv p x‖ ≤ C*Real.exp (-g*|x|)) (huv : |u-v| ≤ 2*e) :
    p u ≤ C*Real.exp (2*g)*Real.exp (-g*|v|) ∧
    p v ≤ C*Real.exp (2*g)*Real.exp (-g*|v|) ∧
    |p u-p v| ≤ (2*e)*(C*Real.exp (2*g)*Real.exp (-g*|v|)) := by
  have hpb (x : ℝ) : p x ≤ C*Real.exp (-g*|x|) :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hb x)
  have hdb (x : ℝ) : ‖deriv p x‖ ≤ C*Real.exp (-g*|x|) := by linarith [hb x, hp x]
  have hlocal (x : ℝ) (hx : |x-v| ≤ 2) :
      C*Real.exp (-g*|x|) ≤ C*Real.exp (2*g)*Real.exp (-g*|v|) := by
    calc
      _ ≤ C*(Real.exp (g*2)*Real.exp (-g*|v|)) :=
        mul_le_mul_of_nonneg_left (exp_abs_shift_bound68 hg hx) hC
      _ = _ := by rw [mul_comm g 2, ← mul_assoc]
  have hbound (x : ℝ) (hx : x ∈ Icc (v-2) (v+2)) :
      ‖deriv p x‖ ≤ C*Real.exp (2*g)*Real.exp (-g*|v|) :=
    (hdb x).trans (hlocal x (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  have hu : u ∈ Icc (v-2) (v+2) := by
    obtain ⟨h1,h2⟩ := abs_le.mp huv
    constructor <;> linarith
  have hv : v ∈ Icc (v-2) (v+2) := ⟨by linarith, by linarith⟩
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hd x) hbound (convex_Icc _ _) hv hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hm
  refine ⟨(hpb u).trans (hlocal u (by linarith)),
    (hpb v).trans (hlocal v (by simp)), ?_⟩
  exact hm.trans ((mul_le_mul_of_nonneg_left huv (by positivity)).trans_eq (by ring))

theorem prod_perturbation68 {ι : Type*} (s : Finset ι) {f h b : ι → ℝ} {e : ℝ}
    (he : 0 ≤ e) (hf0 : ∀ i ∈ s, 0 ≤ f i) (hh0 : ∀ i ∈ s, 0 ≤ h i)
    (hfb : ∀ i ∈ s, f i ≤ b i) (hhb : ∀ i ∈ s, h i ≤ b i)
    (hd : ∀ i ∈ s, |f i-h i| ≤ e*b i) :
    |(∏ i ∈ s, f i)-(∏ i ∈ s, h i)| ≤ (s.card : ℝ)*e*(∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have hfi := hf0 i (Finset.mem_insert_self _ _)
    have hhi := hh0 i (Finset.mem_insert_self _ _)
    have hfbi := hfb i (Finset.mem_insert_self _ _)
    have hhbi := hhb i (Finset.mem_insert_self _ _)
    have hdi := hd i (Finset.mem_insert_self _ _)
    have hfs := fun j hj => hf0 j (Finset.mem_insert_of_mem hj)
    have hhs := fun j hj => hh0 j (Finset.mem_insert_of_mem hj)
    have hfbs := fun j hj => hfb j (Finset.mem_insert_of_mem hj)
    have hhbs := fun j hj => hhb j (Finset.mem_insert_of_mem hj)
    have hds := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    have hIH := ih hfs hhs hfbs hhbs hds
    have hF0 := Finset.prod_nonneg hfs
    have hB0 := Finset.prod_nonneg (fun j hj => (hfs j hj).trans (hfbs j hj))
    have hFB := Finset.prod_le_prod hfs hfbs
    simp only [Finset.prod_insert his, Finset.card_insert_of_notMem his, Nat.cast_add, Nat.cast_one]
    calc
      _ = |(f i-h i)*(∏ j ∈ s, f j)+h i*((∏ j ∈ s, f j)-(∏ j ∈ s, h j))| := by congr 1; ring
      _ ≤ |f i-h i| * (∏ j ∈ s, f j)+h i * |(∏ j ∈ s, f j)-(∏ j ∈ s, h j)| := by
        simpa only [abs_mul, abs_of_nonneg hF0, abs_of_nonneg hhi] using abs_add_le
          ((f i-h i)*(∏ j ∈ s, f j)) (h i*((∏ j ∈ s, f j)-(∏ j ∈ s, h j)))
      _ ≤ (e*b i)*(∏ j ∈ s, b j)+b i*((s.card : ℝ)*e*(∏ j ∈ s, b j)) := by
        apply add_le_add
        · exact mul_le_mul hdi hFB hF0 (mul_nonneg he (hfi.trans hfbi))
        · exact mul_le_mul hhbi hIH (abs_nonneg _) (hfi.trans hfbi)
      _ = _ := by ring

end Luce.Section6
