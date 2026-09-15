import Luce.Section5CycleCutoff
import Mathlib.Tactic

noncomputable section
open Function
open scoped BigOperators
namespace Luce.Section5

def cycleMaximum {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (c : ↥(cycleOrbits R k)) : Fin n :=
  c.val.toFinset.max' (Finset.card_pos.mp (by rw [cycleOrbit_card R k c.val c.property]; omega))

theorem cycleMaximum_mem {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (c : ↥(cycleOrbits R k)) : cycleMaximum R k c ∈ c.val.toFinset :=
  Finset.max'_mem _ _

theorem cycleMaximum_upper {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (c : ↥(cycleOrbits R k)) (v : Fin n) (hv : v ∈ c.val.toFinset) :
    v ≤ cycleMaximum R k c := Finset.le_max' _ _ hv

theorem cycleMaximum_orbit {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (c : ↥(cycleOrbits R k)) : periodicOrbit (R : Fin n → Fin n) (cycleMaximum R k c) = c.val :=
  periodicOrbit_eq_of_mem_cycleOrbit R k c.val c.property _ (cycleMaximum_mem R k c)

theorem cycleMaximum_injective {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ) :
    Injective (cycleMaximum R k) := by
  intro c d h
  apply Subtype.ext
  rw [← cycleMaximum_orbit R k c, ← cycleMaximum_orbit R k d, h]

/-- Each unrooted cycle contributes exactly one largest label. No symmetry
factor remains after this choice of root. -/
def maximumCycleRoots {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.image (cycleMaximum R k)

theorem maximumCycleRoots_card {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ) :
    (maximumCycleRoots R k).card = cycleCount R k := by
  classical
  rw [maximumCycleRoots, Finset.card_image_of_injective _ (cycleMaximum_injective R k)]
  simp [cycleCount]

theorem cycleMaximum_cutoff_iff {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (c : ↥(cycleOrbits R k)) (α : ℝ) :
    c.val.toFinset ⊆ bulkCycleLabelSet n α ↔
      ((cycleMaximum R k c).val : ℝ)+1 ≤ α*n := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp (h (cycleMaximum_mem R k c))).2
  · intro h v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hv' : (v.val : ℝ) ≤ (cycleMaximum R k c).val := by
      exact_mod_cast cycleMaximum_upper R k c v hv
    linarith

/-- Exact cutoff cycle count as a count of maximum roots. -/
theorem bulkCycleCount_eq_maximum_roots {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (α : ℝ) :
    bulkCycleCount R α k = ((maximumCycleRoots R k).filter
      (fun v => (v.val : ℝ)+1 ≤ α*n)).card := by
  classical
  have heq : ((maximumCycleRoots R k).filter (fun v => (v.val : ℝ)+1 ≤ α*n)) =
      (Finset.univ.filter (fun c : ↥(cycleOrbits R k) =>
        c.val.toFinset ⊆ bulkCycleLabelSet n α)).image (cycleMaximum R k) := by
    ext v
    simp only [maximumCycleRoots, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨c, _, rfl⟩, hc⟩
      exact ⟨c, (cycleMaximum_cutoff_iff R k c α).mpr hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, rfl⟩, (cycleMaximum_cutoff_iff R k c α).mp hc⟩
  rw [heq, Finset.card_image_of_injective _ (cycleMaximum_injective R k)]
  simp only [bulkCycleCount, cycleCountWithin, cycleOrbitsWithin]
  exact (Finset.card_bij (fun c hc => (⟨c, (Finset.mem_filter.mp hc).1⟩ : ↥(cycleOrbits R k)))
    (by intro c hc; simpa using (Finset.mem_filter.mp hc).2)
    (by intro c hc d hd h; exact congrArg Subtype.val h)
    (by intro c hc; exact ⟨c.val, Finset.mem_filter.mpr ⟨c.property, (Finset.mem_filter.mp hc).2⟩, rfl⟩))

/-- Exact number of cycles meeting the terminal interval, represented by
their unique largest labels. The natural subtraction is justified by the
finite partition, without a new hypothesis about the cutoff. -/
theorem tailCycleCount_eq_maximum_roots {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (α : ℝ) :
    cycleCount R k - bulkCycleCount R α k =
      ((maximumCycleRoots R k).filter (fun v => α*n < (v.val : ℝ)+1)).card := by
  classical
  rw [← maximumCycleRoots_card R k, bulkCycleCount_eq_maximum_roots]
  have h := Finset.card_filter_add_card_filter_not (s := maximumCycleRoots R k)
    (p := fun v => (v.val : ℝ)+1 ≤ α*n)
  simp only [not_le] at h
  omega

theorem mem_maximumCycleRoots_iff {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ) (v : Fin n) :
    v ∈ maximumCycleRoots R k ↔
      minimalPeriod (R : Fin n → Fin n) v = k+1 ∧
      ∀ u ∈ (periodicOrbit (R : Fin n → Fin n) v).toFinset, u ≤ v := by
  classical
  constructor
  · intro hv
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨minimalPeriod_of_mem_cycleOrbit R k c.val c.property _ (cycleMaximum_mem R k c), ?_⟩
    intro u hu
    rw [cycleMaximum_orbit] at hu
    exact cycleMaximum_upper R k c u hu
  · rintro ⟨hp, hmax⟩
    have hc : periodicOrbit (R : Fin n → Fin n) v ∈ cycleOrbits R k := by
      apply Finset.mem_image.mpr
      exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
    let c : ↥(cycleOrbits R k) := ⟨_, hc⟩
    have heq : cycleMaximum R k c = v := by
      apply le_antisymm (hmax _ (cycleMaximum_mem R k c))
      apply cycleMaximum_upper R k c v
      exact (mem_periodicOrbit_toFinset R v v).mpr
        (self_mem_periodicOrbit (R.injective.mem_periodicPts v))
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, heq⟩

end Luce.Section5
