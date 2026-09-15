import Luce.Section2PredictableProbability
import Luce.Section4Count
import Mathlib.Data.Finset.Powerset

/-! Lemma 4.3 (`lem:slow-label-charge`) of
`fixed_points_sampled_profile.tex`. The sum of the smallest deleted rates is
defined as the minimum total over subsets of the prescribed cardinality.
This definition treats ties without choosing an ordering of equal rates. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Luce

def deletedRateSubsets {n : ℕ} (k : Fin n) : Finset (Finset (Fin n)) :=
  (Finset.univ.erase k).powersetCard (n - k.val - 1)

theorem deletedRateSubsets_nonempty {n : ℕ} (k : Fin n) :
    (deletedRateSubsets k).Nonempty := by
  classical
  apply Finset.powersetCard_nonempty.mpr
  simp only [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- The manuscript's `A_{m-1}^{(-k_m)}`, where `m = n - k.val`. -/
def deletedSmallestRateSum {n : ℕ} (w : Weights n) (k : Fin n) : ℝ :=
  ((deletedRateSubsets k).image w.total).min'
    ((deletedRateSubsets_nonempty k).image _)

theorem deletedSmallestRateSum_attained {n : ℕ} (w : Weights n) (k : Fin n) :
    ∃ s : Finset (Fin n), s ⊆ Finset.univ.erase k ∧
      s.card = n - k.val - 1 ∧ deletedSmallestRateSum w k = w.total s := by
  classical
  obtain ⟨s, hs, he⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((deletedRateSubsets k).image w.total)
      ((deletedRateSubsets_nonempty k).image _))
  exact ⟨s, (Finset.mem_powersetCard.mp hs).1,
    (Finset.mem_powersetCard.mp hs).2, he.symm⟩

theorem deletedSmallestRateSum_nonneg {n : ℕ} (w : Weights n) (k : Fin n) :
    0 ≤ deletedSmallestRateSum w k := by
  obtain ⟨s, _, _, hs⟩ := deletedSmallestRateSum_attained w k
  rw [hs]
  exact w.total_nonneg s

theorem deletedSmallestRateSum_le {n : ℕ} (w : Weights n) (k : Fin n)
    (s : Finset (Fin n)) (hs : s ⊆ Finset.univ.erase k)
    (hc : s.card = n - k.val - 1) : deletedSmallestRateSum w k ≤ w.total s := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨s, Finset.mem_powersetCard.mpr ⟨hs, hc⟩, rfl⟩)

def slowLabelCharge {n : ℕ} (w : Weights n) (k : Fin n) : ℝ :=
  w.rate k / (w.rate k + deletedSmallestRateSum w k)

theorem slowLabelCharge_nonneg {n : ℕ} (w : Weights n) (k : Fin n) :
    0 ≤ slowLabelCharge w k :=
  div_nonneg (w.positive k).le (add_nonneg (w.positive k).le
    (deletedSmallestRateSum_nonneg w k))

theorem remaining_card {n : ℕ} (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (remaining π k).card = n - k.val := by
  classical
  have he : remaining π k = (Finset.Ici k).image π := by
    ext i
    simp only [remaining, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_Ici]
    exact ⟨fun hi => ⟨π.symm i, hi, π.apply_symm_apply i⟩,
      by rintro ⟨j, hj, rfl⟩; simpa using hj⟩
  rw [he, Finset.card_image_of_injective _ π.injective]
  simp

theorem predictableChance_le_slowLabelCharge {n : ℕ} (w : Weights n)
    (π : Equiv.Perm (Fin n)) (k : Fin n) :
    predictableChance w π k ≤ slowLabelCharge w k := by
  classical
  unfold predictableChance Weights.choice
  split_ifs with hk
  · have hmin := deletedSmallestRateSum_le w k ((remaining π k).erase k)
      (Finset.erase_subset_erase k (Finset.subset_univ _))
      (by rw [Finset.card_erase_of_mem hk, remaining_card])
    have hsum := Finset.sum_erase_add (s := remaining π k) w.rate hk
    have hden : w.rate k + deletedSmallestRateSum w k ≤ w.total (remaining π k) := by
      change _ ≤ ∑ i ∈ remaining π k, w.rate i
      change _ ≤ ∑ i ∈ (remaining π k).erase k, w.rate i at hmin
      linarith
    exact div_le_div_of_nonneg_left (w.positive k).le
      (add_pos_of_pos_of_nonneg (w.positive k) (deletedSmallestRateSum_nonneg w k)) hden
  · exact slowLabelCharge_nonneg w k

/-- Lemma 4.3 for any measurable permutation with the exact Luce masses. -/
theorem individual_slow_label_charge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (w : Weights n)
    (π : Ω → Equiv.Perm (Fin n))
    (hπ : @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π)
    (hMass : ∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ)
    (k : Fin n) :
    P.real {ω | (π ω).symm k = k} ≤
      w.rate k / (w.rate k + deletedSmallestRateSum w k) := by
  classical
  have hc := predictable_fixed_point_probability P w π hπ hMass k
  simp only [← predictableChance_formula] at hc
  have he : (∫ ω, predictableChance w (π ω) k ∂P) =
      P.real {ω | (π ω).symm k = k} := by
    rw [← integral_congr_ae hc, integral_condExp (drawHistory_le π hπ k.val)]
    have hm : MeasurableSet {ω | (π ω).symm k = k} :=
      hπ (t := {σ | σ.symm k = k}) trivial
    simpa only [Set.indicator_apply, mem_ofPred_eq, smul_eq_mul, mul_one] using
      integral_indicator_const (μ := P) (1 : ℝ) hm
  rw [← he]
  calc
    _ ≤ ∫ _ω, slowLabelCharge w k ∂P :=
      integral_mono (integrable_finite_state π hπ (fun σ => predictableChance w σ k))
        (integrable_const _) (fun ω => predictableChance_le_slowLabelCharge w (π ω) k)
    _ = _ := by simp [slowLabelCharge]

/-- Lemma 4.3 in the manuscript's one-based rank convention. -/
theorem race_individual_slow_label_charge {n : ℕ} (w : Weights n) (k : Fin n) :
    (exponentialRace w).real {e | raceRank e k = k.val + 1} ≤ slowLabelCharge w k := by
  have he : {e | (raceDraw e).symm k = k} =ᵐ[exponentialRace w]
      {e | raceRank e k = k.val + 1} := by
    filter_upwards [exponentialRace_injective_ae w] with e hinj
    apply propext
    change (raceDraw e).symm k = k ↔ raceRank e k = k.val + 1
    simpa only [mem_ofPred_eq, rankOf_eq_raceRank_for_tail] using
      raceDraw_fixed_iff_rankOf e hinj k
  have h := individual_slow_label_charge (exponentialRace w) w raceDraw
    (measurable_raceDraw n) (raceDraw_mass w) k
  rwa [Measure.real, measure_congr he] at h

end Luce
