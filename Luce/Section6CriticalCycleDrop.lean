import Luce.Section6PathVariation

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem critical_path_variation_sum (k : ℕ) (a b : ℝ) (y : Fin k → ℝ) :
    pathVariation68 k a b y = ∑ j : Fin (k+1),
      |(Fin.cons a y : Fin (k+1) → ℝ) j-(Fin.snoc y b : Fin (k+1) → ℝ) j| := by
  induction k generalizing a b with
  | zero => simp [pathVariation68,Fin.snoc_zero]
  | succ k ih =>
    obtain ⟨s,z,rfl⟩ := Fin.exists_cons y
    simp only [pathVariation68,Fin.cons_zero,Fin.tail_cons,
      ← Fin.cons_snoc_eq_snoc_cons,Fin.sum_univ_succ,Fin.cons_succ,ih]

/-- A closed nonnegative log-coordinate path starting at zero must
have a drop controlled below by the sum of all its vertex heights. -/
theorem critical_cycle_one_drop (k : ℕ) (y : Fin k → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ∃ j : Fin (k+1), (∑ i, y i)/(2*((k : ℝ)+1)^2) ≤
      (Fin.cons 0 y : Fin (k+1) → ℝ) j-(Fin.snoc y 0 : Fin (k+1) → ℝ) j := by
  classical
  let d : Fin (k+1) → ℝ := fun j =>
    (Fin.cons 0 y : Fin (k+1) → ℝ) j-(Fin.snoc y 0 : Fin (k+1) → ℝ) j
  let D := Finset.univ.sup' Finset.univ_nonempty d
  have hd (j : Fin (k+1)) : d j ≤ D := Finset.le_sup' d (Finset.mem_univ j)
  have hsum : ∑ j, d j = 0 := by
    dsimp [d]
    rw [Finset.sum_sub_distrib,Fin.sum_cons,Fin.sum_snoc]
    ring
  have hD : 0 ≤ D := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hd j)
    rw [hsum] at hh
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at hh
    nlinarith
  have habs (j : Fin (k+1)) : |d j| ≤ 2*D-d j := by
    exact abs_le.mpr ⟨by linarith,by linarith [hd j]⟩
  have hvar : pathVariation68 k 0 0 y ≤ 2*((k : ℝ)+1)*D := by
    rw [critical_path_variation_sum]
    change (∑ j, |d j|) ≤ _
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => habs j)
    rw [Finset.sum_sub_distrib,hsum,sub_zero] at hh
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at hh
    nlinarith
  have hyD (i : Fin k) : y i ≤ 2*((k : ℝ)+1)*D := by
    have hh := pathVariation68_vertex k 0 0 y i
    rw [zero_sub,abs_neg,abs_of_nonneg (hy i)] at hh
    exact hh.trans hvar
  have htot : (∑ i, y i) ≤ 2*((k : ℝ)+1)^2*D := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hyD i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    have hp : 0 ≤ 2*((k : ℝ)+1)*D := by positivity
    nlinarith
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty d
  refine ⟨j,?_⟩
  change _ ≤ d j
  have he' : D = d j := he
  rw [← he']
  exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using htot)

end Luce.Section6
