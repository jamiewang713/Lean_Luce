import Luce.Section5FiniteTaylor

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Luce.Section6

set_option backward.isDefEq.respectTransparency false

/-- One extra coordinate in the product is exactly a mixed second moment. -/
theorem coordinate_mul_gap_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (x : ι → ℝ) :
    x i*(∏ j, x j) = ∏ j, x j^(if j=i then 2 else 1 : ℕ) := by
  rw [← Finset.mul_prod_erase Finset.univ x (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => x j^(if j=i then 2 else 1 : ℕ))
      (Finset.mem_univ i)]
  simp only [ite_true]
  have he : (∏ j ∈ Finset.univ.erase i, x j^(if j=i then 2 else 1 : ℕ)) =
      ∏ j ∈ Finset.univ.erase i, x j := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Finset.ne_of_mem_erase hj]
  rw [he]
  ring

theorem markedNormalizedGaps_nonneg_ae {n s : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin s ↪ Fin (Finset.univ \ removed).card) :
    ∀ᵐ old ∂exponentialRace w, ∀ i, 0 ≤ markedNormalizedGaps w removed q old i := by
  filter_upwards [exponentialRace_injective_ae w, exponentialRace_nonnegative_background w]
    with old hold hpos
  intro i
  exact raceNormalizedGaps_nonneg (compactDeletedWeights w removed)
    (compactDeletedClocks removed old) (compactDeletedClocks_injective removed old hold)
    (fun k => hpos (deletedClockLabel removed k)) (q i)

theorem integrable_marked_gap_coordinate_product {n s : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin s ↪ Fin (Finset.univ \ removed).card)
    (i : Fin s) :
    Integrable (fun old => markedNormalizedGaps w removed q old i *
      ∏ j, markedNormalizedGaps w removed q old j) (exponentialRace w) := by
  simp_rw [coordinate_mul_gap_product]
  exact integrable_markedNormalizedGaps_mixed w removed q _

theorem integral_marked_gap_coordinate_product {n s : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin s ↪ Fin (Finset.univ \ removed).card)
    (i : Fin s) :
    (∫ old, markedNormalizedGaps w removed q old i *
      ∏ j, markedNormalizedGaps w removed q old j ∂exponentialRace w) = 2 := by
  simp_rw [coordinate_mul_gap_product]
  rw [integral_markedNormalizedGaps_mixed]
  rw [Finset.prod_eq_single i]
  · norm_num
  · intro j _ hji
    simp [hji]
  · simp

/-- Weighted errors retain each target depth. Replacing these weights by
their maximum would lose the sum of individual endpoint errors. -/
theorem integrable_marked_gap_weighted_error {n s : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin s ↪ Fin (Finset.univ \ removed).card)
    (eps b : Fin s → ℝ) :
    Integrable (fun old => (∑ i, (eps i+b i*markedNormalizedGaps w removed q old i))*
      (∏ i, markedNormalizedGaps w removed q old i)) (exponentialRace w) := by
  have hprod : Integrable (fun old => ∏ i, markedNormalizedGaps w removed q old i)
      (exponentialRace w) := by
    simpa only [pow_one] using integrable_markedNormalizedGaps_mixed w removed q (fun _ => 1)
  simp_rw [Finset.sum_mul, add_mul, mul_assoc]
  exact integrable_finsetSum _ (fun i _ =>
    (hprod.const_mul (eps i)).add ((integrable_marked_gap_coordinate_product w removed q i).const_mul (b i)))

theorem integral_marked_gap_weighted_error {n s : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (q : Fin s ↪ Fin (Finset.univ \ removed).card)
    (eps b : Fin s → ℝ) :
    (∫ old, (∑ i, (eps i+b i*markedNormalizedGaps w removed q old i))*
      (∏ i, markedNormalizedGaps w removed q old i) ∂exponentialRace w) =
      ∑ i, (eps i+2*b i) := by
  have hprod : Integrable (fun old => ∏ i, markedNormalizedGaps w removed q old i)
      (exponentialRace w) := by
    simpa only [pow_one] using integrable_markedNormalizedGaps_mixed w removed q (fun _ => 1)
  simp_rw [Finset.sum_mul, add_mul, mul_assoc]
  have hint (i : Fin s) : Integrable (fun old =>
      eps i*(∏ j, markedNormalizedGaps w removed q old j)+
      b i*(markedNormalizedGaps w removed q old i*(∏ j, markedNormalizedGaps w removed q old j)))
      (exponentialRace w) :=
    (hprod.const_mul (eps i)).add ((integrable_marked_gap_coordinate_product w removed q i).const_mul (b i))
  rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_add (hprod.const_mul (eps i))
    ((integrable_marked_gap_coordinate_product w removed q i).const_mul (b i)),
    integral_const_mul, integral_const_mul, integral_markedNormalizedGaps_prod,
    integral_marked_gap_coordinate_product]
  ring

end Luce.Section6
