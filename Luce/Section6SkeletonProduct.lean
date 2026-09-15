import Luce.Section6SkeletonStart

noncomputable section
namespace Luce.Section6

/-- Total marked rate at selected gaps strictly later than g. -/
def laterSelectedRate {n : ℕ} (S : Finset (Fin n)) (theta : Fin n → ℝ) (g : Fin n) : ℝ :=
  ∑ e ∈ S.filter (fun e => g < e), theta e

theorem later_selected_rate_nonneg {n : ℕ} (S : Finset (Fin n)) (theta : Fin n → ℝ)
    (ht : ∀ e ∈ S, 0 ≤ theta e) (g : Fin n) : 0 ≤ laterSelectedRate S theta g := by
  apply Finset.sum_nonneg
  intro e he
  exact ht e (Finset.mem_filter.mp he).1

/-- Count each selected earlier/later pair once, then group by earlier gap. -/
theorem selected_survival_sum_swap {n : ℕ} (S : Finset (Fin n)) (theta gap : Fin n → ℝ) :
    (∑ e ∈ S, theta e * ∑ g ∈ S.filter (fun g => g < e), gap g) =
      ∑ g ∈ S, laterSelectedRate S theta g * gap g := by
  classical
  unfold laterSelectedRate
  simp only [Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro e he
  by_cases h : g < e <;> simp [h]

theorem gap_start_eq_skeleton_add_selected_indices {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (q : Fin n) (xi : Fin n → ℝ) :
    gapStartFromNormalized w sigma q xi = skeletonStart w sigma S q xi +
      ∑ g ∈ S.filter (fun g => g < q), xi g / orderedRemainingRate w sigma g := by
  have he : (Finset.Iio q).filter (fun g => g ∈ S) = S.filter (fun g => g < q) := by
    ext g
    simp [and_comm]
  simpa only [he] using gap_start_eq_skeleton_add_selected w sigma S q xi

/-- Exact weighted-start decomposition for all selected marks, with the
later-rate term retained even for edges at different corners. -/
theorem selected_weighted_starts {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (theta xi : Fin n → ℝ) :
    (∑ e ∈ S, theta e * gapStartFromNormalized w sigma e xi) =
      (∑ e ∈ S, theta e * skeletonStart w sigma S e xi) +
      ∑ g ∈ S, laterSelectedRate S theta g * (xi g / orderedRemainingRate w sigma g) := by
  simp_rw [gap_start_eq_skeleton_add_selected_indices w sigma S, mul_add]
  rw [Finset.sum_add_distrib, selected_survival_sum_swap]

/-- The product of actual starting-time survival terms factors into the
skeleton survival and one later-mark survival factor per selected spacing. -/
theorem selected_survival_product {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (theta xi : Fin n → ℝ) :
    (∏ e ∈ S, Real.exp (-theta e * gapStartFromNormalized w sigma e xi)) =
      (∏ e ∈ S, Real.exp (-theta e * skeletonStart w sigma S e xi)) *
      ∏ g ∈ S, Real.exp (-laterSelectedRate S theta g * (xi g / orderedRemainingRate w sigma g)) := by
  simp_rw [neg_mul, ← Real.exp_sum]
  rw [← Real.exp_add]
  congr 1
  have he := selected_weighted_starts w sigma S theta xi
  simp only [Finset.sum_neg_distrib]
  linarith

/-- Pointwise identity for the full insertion product, before any integral
or concentration estimate. It does not assert insertion independence. -/
theorem selected_insertion_product_skeleton {n : ℕ} (w : Weights n)
    (sigma : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (theta xi : Fin n → ℝ) :
    (∏ e ∈ S, exponentialGapMass (theta e) (gapStartFromNormalized w sigma e xi)
      (xi e / orderedRemainingRate w sigma e)) =
      (∏ e ∈ S, Real.exp (-theta e * skeletonStart w sigma S e xi)) *
      ∏ g ∈ S, ((1-Real.exp (-theta g*(xi g/orderedRemainingRate w sigma g))) *
        Real.exp (-laterSelectedRate S theta g*(xi g/orderedRemainingRate w sigma g))) := by
  simp_rw [exponentialGapMass_factor, survivalKernel]
  have hs := selected_survival_product w sigma S theta xi
  simp only [← neg_mul]
  simp only [Finset.prod_mul_distrib]
  rw [show (∏ e ∈ S, Real.exp (-(gapStartFromNormalized w sigma e xi) * theta e)) =
      ∏ e ∈ S, Real.exp (-theta e * gapStartFromNormalized w sigma e xi) by
        apply Finset.prod_congr rfl; intro e he; congr 1; ring]
  rw [hs]
  ring

end Luce.Section6
