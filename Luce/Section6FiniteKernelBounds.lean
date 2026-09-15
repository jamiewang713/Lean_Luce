import Luce.Section6FactorialIdealRows
import Luce.Section6FactorialCommonConstants

noncomputable section
open scoped BigOperators
namespace Luce.Section6

theorem finite_local_kernel_bounds {s : ℕ} (side : Fin s → Corner)
    (behavior : Fin s → EndpointBehavior)
    (hg : ∀ c, 0 < localCornerExponent (behavior c))
    (hq : ∀ c, 0 < localCornerQ (side c) (behavior c)) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ c n (a b : Fin n), 0 ≤ localIdealKernel (side c) (behavior c)
        (cornerDistance (side c) a) (cornerDistance (side c) b)) ∧
      (∀ c n (a b : Fin n), 0 ≤ localEnvelopeKernel (side c) (behavior c) d
        (cornerDistance (side c) a) (cornerDistance (side c) b)) ∧
      (∀ c n (a : Fin n), (∑ b : Fin n, localIdealKernel (side c) (behavior c)
        (cornerDistance (side c) a) (cornerDistance (side c) b)) ≤ C) ∧
      (∀ c n (a : Fin n), (∑ b : Fin n, localEnvelopeKernel (side c) (behavior c) d
        (cornerDistance (side c) a) (cornerDistance (side c) b)) ≤ C) ∧
      (∀ c n (a b : Fin n), localIdealKernel (side c) (behavior c)
        (cornerDistance (side c) a) (cornerDistance (side c) b) ≤ C/(cornerDistance (side c) b : ℝ)) ∧
      (∀ c n (a b : Fin n), localEnvelopeKernel (side c) (behavior c) d
        (cornerDistance (side c) a) (cornerDistance (side c) b) ≤ C/(cornerDistance (side c) b : ℝ)) ∧
      (∀ c n (a : Fin n), (∑ b : Fin n,
        (cornerRowRatio (side c) (cornerDistance (side c) a) (cornerDistance (side c) b))^
          (localCornerExponent (behavior c)/2) *
        localIdealKernel (side c) (behavior c)
          (cornerDistance (side c) a) (cornerDistance (side c) b)) ≤ C) := by
  classical
  have hi (c : Fin s) := local_ideal_matrix_bounds (side c) (behavior c) (hq c) (hg c)
    (kappa := localCornerExponent (behavior c)/2) (by linarith [hg c])
  have he (c : Fin s) := local_envelope_matrix_bounds (side c) (behavior c) hd (hg c)
    (kappa := 0) (hg c)
  choose CI hCI hI hIr hIt hIw using hi
  choose CH hCH hH hHr hHt hHw using he
  obtain ⟨C, hC, hbound⟩ := factorial_finite_common_upper_bound (fun c => max (CI c) (CH c))
    (fun c => (zero_le_one.trans (hCI c)).trans (le_max_left _ _))
  have hIC (c : Fin s) : CI c ≤ C := (le_max_left _ _).trans (hbound c)
  have hHC (c : Fin s) : CH c ≤ C := (le_max_right _ _).trans (hbound c)
  refine ⟨C, hC, hI, hH, ?_, ?_, ?_, ?_, ?_⟩
  · intro c n a
    exact (hIr c n a).trans (hIC c)
  · intro c n a
    exact (hHr c n a).trans (hHC c)
  · intro c n a b
    exact (hIt c n a b).trans (div_le_div_of_nonneg_right (hIC c) (Nat.cast_nonneg _))
  · intro c n a b
    exact (hHt c n a b).trans (div_le_div_of_nonneg_right (hHC c) (Nat.cast_nonneg _))
  · intro c n a
    exact (hIw c n a).trans (hIC c)

end Luce.Section6
