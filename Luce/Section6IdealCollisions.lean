import Luce.Section6LogKernelRows
import Luce.Section6LogGridComparison
import Luce.Section6CollisionCycleTests
import Luce.Section6ExcursionDepthSums

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem noninjective_cycle_sum68 {α : Type*} [Fintype α]
    (F : α → α → ℝ) (hF : ∀ a b, 0 ≤ F a b)
    (v : α → ℝ) (hv : ∀ a, 0 ≤ v a) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b, F a b ≤ C) (htarget : ∀ a b, F a b ≤ C*v b) (k : ℕ) :
    (∑ x : Fin (k+1) → α, if ¬Function.Injective x then collisionCycleWeight F k x else 0) ≤
      ((k : ℝ)+1)^2*(C^(k+1)*(∑ a, (v a)^2)) := by
  classical
  have hW (x : Fin (k+1) → α) := collisionCycleWeight_nonneg hF k x
  have hR : 0 ≤ C^(k+1)*(∑ a, (v a)^2) := by positivity
  have hpair (i j : Fin (k+1)) (hij : i ≠ j) :
      (∑ x : Fin (k+1) → α, if i ≠ j ∧ x i = x j then collisionCycleWeight F k x else 0) ≤
        C^(k+1)*(∑ a, (v a)^2) := by
    have h := collision_cycle_two_test_bound F hF v hv hC hrow htarget k i j hij
      (fun a b => if a = b then 1 else 0) (fun a b => by split_ifs <;> norm_num)
    simpa [hij, mul_ite, ite_mul, pow_two] using h
  calc
    _ ≤ ∑ x : Fin (k+1) → α, ∑ i : Fin (k+1), ∑ j : Fin (k+1),
        if i ≠ j ∧ x i = x j then collisionCycleWeight F k x else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases h : Function.Injective x
      · rw [if_neg (not_not.mpr h)]
        exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by split_ifs <;>
          first | exact hW x | rfl))
      · rw [if_pos h]
        obtain ⟨i,j,he,hij⟩ := Function.not_injective_iff.mp h
        have hinner : collisionCycleWeight F k x ≤ ∑ j' : Fin (k+1),
            if i ≠ j' ∧ x i = x j' then collisionCycleWeight F k x else 0 := by
          have hh := Finset.single_le_sum (s := Finset.univ)
            (f := fun j' => if i ≠ j' ∧ x i = x j' then collisionCycleWeight F k x else 0)
            (fun j' _ => by split_ifs <;> first | exact hW x | rfl) (Finset.mem_univ j)
          simpa only [if_pos (show i ≠ j ∧ x i = x j from ⟨hij,he⟩)] using hh
        exact hinner.trans (Finset.single_le_sum
          (f := fun i' => ∑ j' : Fin (k+1), if i' ≠ j' ∧ x i' = x j' then collisionCycleWeight F k x else 0)
          (fun i' _ => Finset.sum_nonneg (fun j' _ => by split_ifs <;> first | exact hW x | rfl))
          (Finset.mem_univ i))
    _ = ∑ i : Fin (k+1), ∑ j : Fin (k+1), ∑ x : Fin (k+1) → α,
        if i ≠ j ∧ x i = x j then collisionCycleWeight F k x else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ ≤ ∑ _i : Fin (k+1), ∑ _j : Fin (k+1), C^(k+1)*(∑ a, (v a)^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j; simpa using hR
      · exact hpair i j hij
    _ = _ := by simp; ring

theorem reciprocal_square_sum68 {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ m : ↥(Finset.Icc A B), (1/(m.val : ℝ))^2) ≤ 2/(A : ℝ) := by
  have ha : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hs := left_excursion_depth_sum (kappa := 1) (by norm_num) hA hAB
  norm_num [Real.rpow_neg, Real.rpow_two, one_div] at hs
  rw [Finset.sum_coe_sort (Finset.Icc A B) (fun m : ℕ => (1/(m : ℝ))^2)]
  apply (le_div_iff₀ ha).mpr
  simpa [mul_comm, one_div, inv_pow] using hs

theorem collision_log_weight68 (p : ℝ → ℝ) {A B k : ℕ} (a : IdealDepthTuple A B k) :
    collisionCycleWeight (fun u v : ↥(Finset.Icc A B) => logKernel68 p u.val v.val) k a =
      closedLogCycleWeight p k (fun j => Real.log ((a j).val : ℝ))*(∏ j, 1/((a j).val : ℝ)) := by
  unfold collisionCycleWeight logKernel68 closedLogCycleWeight
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, one_mul]
  congr 1
  exact Equiv.prod_comp (finRotate (k+1)) (fun j => ((a j).val : ℝ)⁻¹)

def logDistinctTrace68 (p : ℝ → ℝ) (k A B : ℕ) : ℝ := by
  classical
  exact (∑ a ∈ Finset.univ.filter (Function.Injective : IdealDepthTuple A B k → Prop),
    collisionCycleWeight (fun u v : ↥(Finset.Icc A B) => logKernel68 p u.val v.val) k a)/((k : ℝ)+1)

def logCollisionConstant68 (C g : ℝ) (k : ℕ) : ℝ :=
  2*((k : ℝ)+1)^2*(C+(2*C*Real.exp g)*(2/g)+1)^(k+1)

theorem logDistinctTrace68_comparison {p : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x)
    {C g : ℝ} (hC : 0 ≤ C) (hg : 0 < g) (hb : ∀ x, p x ≤ C*Real.exp (-g*|x|))
    (k : ℕ) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    |logDistinctTrace68 p k A B-logGridTrace68 p k A B| ≤ logCollisionConstant68 C g k/(A : ℝ) := by
  classical
  let F : ↥(Finset.Icc A B) → ↥(Finset.Icc A B) → ℝ := fun a b => logKernel68 p a.val b.val
  let v : ↥(Finset.Icc A B) → ℝ := fun a => 1/(a.val : ℝ)
  let M := C+(2*C*Real.exp g)*(2/g)+1
  have hF : ∀ a b, 0 ≤ F a b := fun a b => div_nonneg (hp _) (Nat.cast_nonneg _)
  have hv : ∀ a, 0 ≤ v a := fun _ => by dsimp [v]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hCM : C ≤ M := by
    have hh : 0 ≤ (2*C*Real.exp g)*(2/g) := by positivity
    dsimp [M]
    linarith
  have hrow (a : ↥(Finset.Icc A B)) : ∑ b, F a b ≤ M :=
    (log_kernel_row68 hp hC hg hb hA (Real.log (a.val : ℝ))).trans (by dsimp [M]; linarith)
  have htarget (a b : ↥(Finset.Icc A B)) : F a b ≤ M*v b :=
    (log_kernel_target68 hC hg.le hb a.val b.val).trans (mul_le_mul_of_nonneg_right hCM (hv b))
  have hbad := (noninjective_cycle_sum68 F hF v hv hM hrow htarget k).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (reciprocal_square_sum68 hA hAB)
      (pow_nonneg hM _)) (sq_nonneg _))
  have hsplit : (∑ a ∈ Finset.univ.filter (Function.Injective : IdealDepthTuple A B k → Prop),
        collisionCycleWeight F k a) +
      (∑ a : IdealDepthTuple A B k, if ¬Function.Injective a then collisionCycleWeight F k a else 0) =
      ∑ a : IdealDepthTuple A B k, collisionCycleWeight F k a := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : Function.Injective a <;> simp [h]
  have hbad0 : 0 ≤ ∑ a : IdealDepthTuple A B k,
      if ¬Function.Injective a then collisionCycleWeight F k a else 0 :=
    Finset.sum_nonneg (fun a _ => by split_ifs <;> first | exact collisionCycleWeight_nonneg hF _ _ | rfl)
  unfold logDistinctTrace68 logGridTrace68
  simp_rw [← collision_log_weight68]
  change |(_ : ℝ)/((k : ℝ)+1)-(_ : ℝ)/((k : ℝ)+1)| ≤ _
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < (k : ℝ)+1)]
  have he : (∑ a ∈ Finset.univ.filter (Function.Injective : IdealDepthTuple A B k → Prop),
      collisionCycleWeight F k a)-(∑ a : IdealDepthTuple A B k, collisionCycleWeight F k a) =
      -(∑ a : IdealDepthTuple A B k, if ¬Function.Injective a then collisionCycleWeight F k a else 0) := by linarith
  rw [he, abs_neg, abs_of_nonneg hbad0]
  apply (div_le_self hbad0 (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ)+1)).trans
  convert hbad using 1
  · apply Finset.sum_congr rfl
    intro a _
    by_cases h : Function.Injective a <;> simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false]
  · dsimp [logCollisionConstant68, M]
    ring

end Luce.Section6
