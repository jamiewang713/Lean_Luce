import Luce.Section6DensityPerturbation

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem closedLogCycleWeight_const_mul68 (p : ℝ → ℝ) (C : ℝ) (k : ℕ) (x : Fin (k+1) → ℝ) :
    closedLogCycleWeight (fun t => C*p t) k x = C^(k+1)*closedLogCycleWeight p k x := by
  unfold closedLogCycleWeight
  rw [Finset.prod_mul_distrib]
  simp

theorem closed_cycle_perturbation68 {p : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hd : Differentiable ℝ p) {C g e : ℝ} (hC : 0 ≤ C) (hg : 0 ≤ g)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hb : ∀ x, p x+‖deriv p x‖ ≤ C*Real.exp (-g*|x|))
    (k : ℕ) (a x : Fin (k+1) → ℝ) (hax : ∀ j, |a j-x j| ≤ e) :
    |closedLogCycleWeight p k a-closedLogCycleWeight p k x| ≤
      ((k : ℝ)+1)*(2*e)*(C*Real.exp (2*g))^(k+1)*
        closedLogCycleWeight (fun t => Real.exp (-g*|t|)) k x ∧
    closedLogCycleWeight p k x ≤ (C*Real.exp (2*g))^(k+1)*
        closedLogCycleWeight (fun t => Real.exp (-g*|t|)) k x := by
  have he (j : Fin (k+1)) : |(a j-a (finRotate (k+1) j))-(x j-x (finRotate (k+1) j))| ≤ 2*e := by
    have ht := abs_sub_le (a j-x j) 0 (a (finRotate (k+1) j)-x (finRotate (k+1) j))
    simp only [sub_zero, zero_sub, abs_neg] at ht
    have hid : (a j-a (finRotate (k+1) j))-(x j-x (finRotate (k+1) j)) =
        (a j-x j)-(a (finRotate (k+1) j)-x (finRotate (k+1) j)) := by ring
    rw [hid]
    linarith [hax j, hax (finRotate (k+1) j)]
  have hpert (j : Fin (k+1)) := density_perturbation68 hp hd hC hg he0 he1 hb (he j)
  have hprod : (∏ j : Fin (k+1), C*Real.exp (2*g)*Real.exp (-g*|x j-x (finRotate (k+1) j)|)) =
      (C*Real.exp (2*g))^(k+1)*closedLogCycleWeight (fun t => Real.exp (-g*|t|)) k x :=
    closedLogCycleWeight_const_mul68 (fun t => Real.exp (-g*|t|)) (C*Real.exp (2*g)) k x
  constructor
  · have h := prod_perturbation68 Finset.univ (by positivity : 0 ≤ 2*e)
      (fun j _ => hp (a j-a (finRotate (k+1) j))) (fun j _ => hp (x j-x (finRotate (k+1) j)))
      (fun j _ => (hpert j).1) (fun j _ => (hpert j).2.1) (fun j _ => (hpert j).2.2)
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one, hprod] at h
    simpa only [closedLogCycleWeight, mul_assoc] using h
  · have h := Finset.prod_le_prod (fun j (_ : j ∈ (Finset.univ : Finset (Fin (k+1)))) =>
      hp (x j-x (finRotate (k+1) j))) (fun j _ => (hpert j).2.1)
    rw [hprod] at h
    exact h

def logCellCorrection68 (m : ℕ) : ℝ := 1/((m : ℝ)*logCellWidth68 m)

theorem logCellCorrection68_bounds {A m : ℕ} (hA : 1 ≤ A) (hAm : A ≤ m) :
    1 ≤ logCellCorrection68 m ∧ logCellCorrection68 m ≤ 1+1/(A : ℝ) := by
  have hm : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hA0 : 0 < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hw := logCellWidth68_pos hm
  have hwb := logCellWidth68_bounds hm
  have hprod : 0 < (m : ℝ)*logCellWidth68 m := mul_pos hmR hw
  unfold logCellCorrection68
  constructor
  · apply (le_div_iff₀ hprod).mpr
    have h := (le_div_iff₀ hmR).mp hwb.2
    nlinarith
  · have h : 1 ≤ ((m : ℝ)+1)*logCellWidth68 m := by
      have hh := (div_le_iff₀ (show 0 < (m : ℝ)+1 by positivity)).mp hwb.1
      nlinarith
    have hh : 1/((m : ℝ)*logCellWidth68 m) ≤ 1+1/(m : ℝ) := by
      apply (div_le_iff₀ hprod).mpr
      have he : (1+1/(m : ℝ))*((m : ℝ)*logCellWidth68 m) = ((m : ℝ)+1)*logCellWidth68 m := by
        field_simp
      rwa [he]
    have hinv : 1/(m : ℝ) ≤ 1/(A : ℝ) := one_div_le_one_div_of_le hA0 (by exact_mod_cast hAm)
    linarith

theorem logCellCorrection68_product_bounds {A B k : ℕ} (hA : 1 ≤ A) (a : IdealDepthTuple A B k) :
    0 ≤ (∏ j, logCellCorrection68 (a j).val) ∧
    (∏ j, logCellCorrection68 (a j).val) ≤ (2 : ℝ)^(k+1) ∧
    |(∏ j, logCellCorrection68 (a j).val)-1| ≤ ((k : ℝ)+1)*(1/(A : ℝ))*(2 : ℝ)^(k+1) := by
  have he : 1/(A : ℝ) ≤ 1 := (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
    (by exact_mod_cast hA)).trans_eq (by norm_num)
  have hb (j : Fin (k+1)) := logCellCorrection68_bounds hA (Finset.mem_Icc.mp (a j).property).1
  have hz (j : Fin (k+1)) : 0 ≤ logCellCorrection68 (a j).val := zero_le_one.trans (hb j).1
  have hu (j : Fin (k+1)) : logCellCorrection68 (a j).val ≤ 2 := by linarith [(hb j).2]
  refine ⟨Finset.prod_nonneg (fun j _ => hz j), ?_, ?_⟩
  · simpa using Finset.prod_le_prod (s := Finset.univ) (fun j _ => hz j) (fun j _ => hu j)
  · have hd (j : Fin (k+1)) : |logCellCorrection68 (a j).val-1| ≤ (1/(A : ℝ))*2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hb j).1)]
      have h0 : 0 ≤ 1/(A : ℝ) := by positivity
      linarith [(hb j).2]
    simpa using prod_perturbation68 Finset.univ (by positivity : 0 ≤ 1/(A : ℝ))
      (fun j _ => hz j) (fun _ _ => zero_le_one) (fun j _ => hu j)
      (fun _ _ => (by norm_num : (1 : ℝ) ≤ 2)) (fun j _ => hd j)

end Luce.Section6
