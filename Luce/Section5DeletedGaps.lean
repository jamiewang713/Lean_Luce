import Luce.Section5MarkedGaps

/-!
# Deleted-clock compaction and consecutive gap integrals

The compacted clock family consists of exactly the unmarked coordinates,
with their original rates. Its law is proved to be the corresponding
exponential product law. The insertion kernels of `Section5MarkedGaps`
are identified with the actual consecutive order-statistic intervals in
`fixed_points.tex:1017–1048`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators

namespace Luce
attribute [local instance] Classical.propDecidable

def deletedClockLabel {n : ℕ} (removed : Finset (Fin n))
    (k : Fin (Finset.univ \ removed).card) : Fin n :=
  ((Finset.univ \ removed).equivFin.symm k).val

lemma deletedClockLabel_injective {n : ℕ} (removed : Finset (Fin n)) :
    Injective (deletedClockLabel removed) := by
  intro a b hab
  apply (Finset.univ \ removed).equivFin.symm.injective
  exact Subtype.ext hab

def compactDeletedClocks {n : ℕ} (removed : Finset (Fin n)) (old : Fin n → ℝ) :
    Fin (Finset.univ \ removed).card → ℝ := fun k => old (deletedClockLabel removed k)

def compactDeletedWeights {n : ℕ} (w : Weights n) (removed : Finset (Fin n)) :
    Weights (Finset.univ \ removed).card :=
  ⟨fun k => w.rate (deletedClockLabel removed k), fun k => w.positive _⟩

lemma compactDeletedClocks_measurable {n : ℕ} (removed : Finset (Fin n)) :
    Measurable (compactDeletedClocks removed) :=
  measurable_pi_lambda _ (fun k => measurable_pi_apply (deletedClockLabel removed k))

/-- Exact equality of the actual unmarked clock law with the compacted
exponential race. No independence hypothesis is added. -/
theorem compactDeletedClocks_measurePreserving {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) :
    MeasurePreserving (compactDeletedClocks removed) (exponentialRace w)
      (exponentialRace (compactDeletedWeights w removed)) := by
  refine ⟨compactDeletedClocks_measurable removed, ?_⟩
  have hind := (exponentialRace_independent w).precomp (deletedClockLabel_injective removed)
  have h := hind.map_fun_eq_pi_map
    (fun k => (measurable_pi_apply (deletedClockLabel removed k)).aemeasurable)
  change (exponentialRace w).map (compactDeletedClocks removed) = _ at h
  rw [h]
  unfold exponentialRace
  congr 1
  funext k
  exact (exponentialRace_eval w (deletedClockLabel removed k)).map_eq

lemma compactDeletedClocks_injective {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (hold : Injective old) : Injective (compactDeletedClocks removed old) :=
  hold.comp (deletedClockLabel_injective removed)

lemma compactDeletedClocks_card {n : ℕ} (removed : Finset (Fin n)) :
    (Finset.univ \ removed).card = n - removed.card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ removed), Finset.card_univ, Fintype.card_fin]

lemma compactMarkedClocks_card {n r : ℕ} (u : Fin r → Fin n) (hu : Injective u) :
    (Finset.univ \ Finset.univ.image u).card = n - r := by
  rw [compactDeletedClocks_card, Finset.card_image_of_injective _ hu,
    Finset.card_univ, Fintype.card_fin]

/-- Relabeling the remaining coordinates neither changes a before-count
nor introduces multiplicities. -/
theorem clockBeforeCount_compactDeletedClocks {n : ℕ} (removed : Finset (Fin n))
    (old : Fin n → ℝ) (t : ℝ) :
    clockBeforeCount (compactDeletedClocks removed old) t = deletedBeforeCount removed old t := by
  unfold clockBeforeCount deletedBeforeCount
  simp only [Finset.card_filter]
  have h := (Finset.univ \ removed).equivFin.symm.sum_comp
    (fun i => if old i.val < t then (1 : ℕ) else 0)
  exact h.trans (Finset.sum_coe_sort _ (fun i => if old i < t then (1 : ℕ) else 0))

/-- The finite gap's lower endpoint, with `T₀=0`; `q=0` is the first gap. -/
def consecutiveGapLower {m : ℕ} (times : Fin m → ℝ) (htimes : Injective times)
    (q : Fin m) : ℝ :=
  if h : q.val = 0 then 0 else arrivalTime times htimes ⟨q.val - 1, by omega⟩

lemma consecutiveGapLower_nonneg {m : ℕ} (times : Fin m → ℝ) (htimes : Injective times)
    (hpos : ∀ i, 0 ≤ times i) (q : Fin m) : 0 ≤ consecutiveGapLower times htimes q := by
  unfold consecutiveGapLower
  split_ifs
  · exact le_rfl
  · exact hpos _

/-- Exact order-statistic description of each nonterminal count gap.
The only excluded times are the finitely many old clock values. -/
theorem mem_consecutiveGap_iff_count {m : ℕ} (times : Fin m → ℝ)
    (htimes : Injective times) (hpos : ∀ i, 0 ≤ times i) (q : Fin m) (t : ℝ)
    (havoid : ∀ i, t ≠ times i) :
    t ∈ Ioo (consecutiveGapLower times htimes q) (arrivalTime times htimes q) ↔
      0 < t ∧ clockBeforeCount times t = q.val := by
  have hu := lt_arrivalTime_iff_clockBeforeCount times htimes q t
    (havoid (drawPermutation times htimes q))
  rw [Set.mem_Ioo, hu]
  by_cases hq : q.val = 0
  · simp only [consecutiveGapLower, hq, dite_true]
    exact and_congr_right (fun _ => Nat.lt_one_iff)
  · have hidx : q.val - 1 < m := by omega
    have hl := arrivalTime_lt_iff_clockBeforeCount times htimes ⟨q.val - 1, hidx⟩ t
    simp only [consecutiveGapLower, hq, dite_false, hl, Fin.val_mk]
    constructor
    · intro ht
      have hlt : arrivalTime times htimes ⟨q.val - 1, hidx⟩ < t := hl.mpr ht.1
      exact ⟨(hpos _).trans_lt hlt, by omega⟩
    · intro ht
      exact ⟨by omega, by omega⟩

/-- Exact correspondence with the source's unmarked open gap, including
the initial lower endpoint. -/
theorem deletedGapKernel_eq_interval_measure {n : ℕ} (w : Weights n)
    (removed : Finset (Fin n)) (old : Fin n → ℝ) (hold : Injective old)
    (hpos : ∀ i, 0 ≤ old i) (i : Fin n) (q : Fin (Finset.univ \ removed).card) :
    deletedGapKernel w removed old i q.val = expMeasure (w.rate i)
      (Ioo (consecutiveGapLower (compactDeletedClocks removed old)
        (compactDeletedClocks_injective removed old hold) q)
        (arrivalTime (compactDeletedClocks removed old)
          (compactDeletedClocks_injective removed old hold) q)) := by
  unfold deletedGapKernel
  apply measure_congr
  filter_upwards [exponential_avoids_background (compactDeletedClocks removed old) (w.rate i)] with t ht
  apply propext
  have h := mem_consecutiveGap_iff_count (compactDeletedClocks removed old)
    (compactDeletedClocks_injective removed old hold) (fun k => hpos _) q t ht
  rw [clockBeforeCount_compactDeletedClocks] at h
  exact h.symm

end Luce
