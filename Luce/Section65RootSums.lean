import Luce.Section6Lemma67
import Luce.Section5FiniteStatistic

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem selectedRootCycleCount_eq_sum65 {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (S : Finset (Fin n)) :
    selectedRootCycleCount R k S = ∑ v ∈ S, selectedRootCycleCount R k {v} := by
  classical
  have he : selectedRootCycleCount R k S =
      ((Section5.maximumCycleRoots R k).filter (fun v => v ∈ S)).card := by
    unfold selectedRootCycleCount
    convert filtered_cycle_count_eq_root_count R k (fun v _ => v ∈ S) using 1 <;>
      congr 1 <;> ext c <;> simp
  rw [he]
  simp_rw [selected_root_singleton67]
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  congr 1
  ext v
  simp [and_comm]

theorem selectedRootCycleCount_expectation_sum65 {n : ℕ} (w : Weights n)
    (k : ℕ) (S : Finset (Fin n)) :
    (∫ z, (selectedRootCycleCount (raceRankPermutation z) k S : ℝ) ∂exponentialRace w) =
      ∑ v ∈ S, ∫ z, (selectedRootCycleCount (raceRankPermutation z) k {v} : ℝ)
        ∂exponentialRace w := by
  simp_rw [selectedRootCycleCount_eq_sum65 (S := S),Nat.cast_sum]
  exact integral_finsetSum _ (fun v _ =>
    integrable_race_permutation_statistic w (fun R => (selectedRootCycleCount R k {v} : ℝ)))

theorem selectedRootCycleCount_harmonic65 {n : ℕ} (w : Weights n)
    (side : Corner) (k : ℕ) (S : Finset (Fin n)) {C A B : ℝ}
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hAB : A ≤ B)
    (hS : ∀ v ∈ S, A ≤ (cornerDistance side v : ℝ) ∧ (cornerDistance side v : ℝ) ≤ B)
    (hroot : ∀ v ∈ S,
      (∫ z, (selectedRootCycleCount (raceRankPermutation z) k {v} : ℝ) ∂exponentialRace w) ≤
        C/(cornerDistance side v : ℝ)) :
    (∫ z, (selectedRootCycleCount (raceRankPermutation z) k S : ℝ) ∂exponentialRace w) ≤
      C*(1+Real.log (B/A)) := by
  classical
  rw [selectedRootCycleCount_expectation_sum65]
  calc
    _ ≤ ∑ v ∈ S, C/(cornerDistance side v : ℝ) := Finset.sum_le_sum hroot
    _ = C * ∑ m ∈ S.image (cornerDistance side), 1/(m : ℝ) := by
      rw [Finset.sum_image (fun a _ b _ h => cornerDistance_injective67 side h),Finset.mul_sum]
      simp only [mul_one_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_real_subset67 _ hA hAB (by
      intro m hm
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
      exact hS v hv)) hC

end Luce.Section6
