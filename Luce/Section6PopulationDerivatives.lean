import Luce.Section6PopulationFinite

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem survivalKernel_hasDerivAt_time (a t : ℝ) :
    HasDerivAt (fun s => survivalKernel s a) (-a * survivalKernel t a) t := by
  simpa [survivalKernel, neg_mul, mul_comm] using
    (((hasDerivAt_id t).mul_const (-a)).exp)

/-- Differentiate the exact finite population, never an asymptotic error. -/
theorem populationD_hasDerivAt {n : ℕ} (w : Weights n) (r : ℕ) (t : ℝ) :
    HasDerivAt (populationD w r) (-populationD w (r+1) t) t := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun (i : Fin n) _ => (survivalKernel_hasDerivAt_time (w.rate i) t).const_mul
      (w.rate i ^ r))).div_const (n : ℝ)
  have heq : (∑ i, w.rate i ^ r * (-w.rate i * survivalKernel t (w.rate i))) / (n : ℝ) =
      -populationD w (r+1) t := by
    have hs : (∑ i, w.rate i ^ r * (-w.rate i * survivalKernel t (w.rate i))) =
        -(∑ i, w.rate i ^ (r+1) * survivalKernel t (w.rate i)) := by
      calc
        _ = ∑ i, -(w.rate i ^ (r+1) * survivalKernel t (w.rate i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [pow_succ]
          ring
        _ = _ := Finset.sum_neg_distrib _
    rw [hs, neg_div]
    rfl
  rw [heq] at h
  exact h

theorem populationH_hasDerivAt {n : ℕ} (w : Weights n) (t : ℝ) :
    HasDerivAt (populationH w) (-populationD w 1 t) t := by
  have heq : populationD w 0 = populationH w := by
    funext s
    simp [populationD, populationH]
  simpa only [heq, Nat.zero_add] using populationD_hasDerivAt w 0 t

theorem populationG_hasDerivAt {n : ℕ} (hn : 0 < n) (w : Weights n) (t : ℝ) :
    HasDerivAt (populationG w) (populationD w 1 t) t := by
  have heq : populationG w = fun s => 1-populationH w s := by
    funext s
    exact populationG_eq_one_sub_H hn w s
  rw [heq]
  simpa using (populationH_hasDerivAt w t).const_sub 1

end Luce.Section6
