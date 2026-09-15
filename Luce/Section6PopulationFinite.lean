import Luce.Section6Sampling
import Luce.Section3ProfileKernels

/-! Exact finite-population transforms and deletion estimates for Section 6.
The divisor stays n after deletion. None of these results requires mean-one
normalization or any asymptotic profile condition. -/
noncomputable section
open scoped BigOperators
namespace Luce.Section6

def populationH {n : ℕ} (w : Weights n) (t : ℝ) : ℝ :=
  (∑ i, survivalKernel t (w.rate i)) / n

def populationG {n : ℕ} (w : Weights n) (t : ℝ) : ℝ :=
  (∑ i, (1-survivalKernel t (w.rate i))) / n

def populationD {n : ℕ} (w : Weights n) (r : ℕ) (t : ℝ) : ℝ :=
  (∑ i, w.rate i ^ r * survivalKernel t (w.rate i)) / n

def deletedH {n : ℕ} (w : Weights n) (removed : Finset (Fin n)) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ \ removed, survivalKernel t (w.rate i)) / n

/-- After deletion this is the arrival sum, not 1 minus deletedH. -/
def deletedG {n : ℕ} (w : Weights n) (removed : Finset (Fin n)) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ \ removed, (1-survivalKernel t (w.rate i))) / n

def deletedD {n : ℕ} (w : Weights n) (removed : Finset (Fin n)) (r : ℕ) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ \ removed, w.rate i ^ r * survivalKernel t (w.rate i)) / n

theorem populationG_eq_one_sub_H {n : ℕ} (hn : 0 < n) (w : Weights n) (t : ℝ) :
    populationG w t = 1-populationH w t := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [populationG, populationH, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [sub_div, div_self hn0]

theorem finite_average_deletion {n : ℕ} (removed : Finset (Fin n)) (g : Fin n → ℝ) :
    (∑ i, g i) / (n : ℝ) - (∑ i ∈ Finset.univ \ removed, g i) / n =
      (∑ i ∈ removed, g i) / n := by
  have h := Finset.sum_sdiff (Finset.subset_univ removed) (f := g)
  rw [← h]
  ring

theorem finite_average_deletion_bound {n r : ℕ} (removed : Finset (Fin n))
    (hr : removed.card ≤ r) (g : Fin n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ i, 0 ≤ g i ∧ g i ≤ M) :
    |(∑ i, g i) / (n : ℝ) - (∑ i ∈ Finset.univ \ removed, g i) / n| ≤
      (r : ℝ) * M / n := by
  rw [finite_average_deletion,
    abs_of_nonneg (div_nonneg (Finset.sum_nonneg fun i _ => (hg i).1) (Nat.cast_nonneg n))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    _ ≤ ∑ _i ∈ removed, M := Finset.sum_le_sum fun i _ => (hg i).2
    _ = (removed.card : ℝ) * M := by simp
    _ ≤ (r : ℝ) * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hM

theorem populationH_deletion_bound {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (hr : removed.card ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    |populationH w t - deletedH w removed t| ≤ (r : ℝ) / n := by
  simpa only [populationH, deletedH, mul_one] using
    finite_average_deletion_bound removed hr (fun i => survivalKernel t (w.rate i))
      (M := 1) zero_le_one (fun i =>
        ⟨(survivalKernel_pos _ _).le, survivalKernel_le_one ht (w.positive i).le⟩)

theorem populationG_deletion_bound {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (hr : removed.card ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    |populationG w t - deletedG w removed t| ≤ (r : ℝ) / n := by
  simpa only [populationG, deletedG, mul_one] using
    finite_average_deletion_bound removed hr (fun i => 1-survivalKernel t (w.rate i))
      (M := 1) zero_le_one (fun i =>
        ⟨sub_nonneg.mpr (survivalKernel_le_one ht (w.positive i).le),
          sub_le_self _ (survivalKernel_pos _ _).le⟩)

/-- Sharp supremum bound on a weighted exponential summand. -/
theorem rateKernel_le_exp_neg_one_div {t a : ℝ} (ht : 0 < t) :
    rateKernel t a ≤ Real.exp (-1) / t := by
  apply (le_div_iff₀ ht).mpr
  have h := Real.mul_exp_neg_le_exp_neg_one (t*a)
  simpa [rateKernel, survivalKernel, neg_mul, mul_assoc, mul_comm, mul_left_comm] using h

/-- The manuscript's r/(e*n*t) deletion bound, uniform in deleted labels. -/
theorem populationD_one_deletion_bound {n r : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (hr : removed.card ≤ r) {t : ℝ} (ht : 0 < t) :
    |populationD w 1 t - deletedD w removed 1 t| ≤
      (r : ℝ) * (Real.exp (-1) / t) / n := by
  simpa only [populationD, deletedD, pow_one, rateKernel] using
    finite_average_deletion_bound removed hr (fun i => rateKernel t (w.rate i))
      (div_nonneg (Real.exp_pos _).le ht.le) (fun i =>
        ⟨rateKernel_nonneg (w.positive i).le, rateKernel_le_exp_neg_one_div ht⟩)

end Luce.Section6
