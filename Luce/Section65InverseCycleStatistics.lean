import Luce.Section6FilteredCycleCount
import Luce.Section6ContractDefinitions
import Mathlib.GroupTheory.Perm.Cycle.Basic

noncomputable section
open Function
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

theorem periodicOrbit_finset_sameCycle65 {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α) (x y : α) :
    y ∈ (periodicOrbit (R : α → α) x).toFinset ↔ R.SameCycle x y := by
  have hx : x ∈ periodicPts (R : α → α) := by
    exact R.injective.mem_periodicPts x
  rw [Section5.mem_periodicOrbit_toFinset, mem_periodicOrbit_iff hx]
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨(n : ℤ), by simpa only [Equiv.Perm.coe_pow, zpow_natCast] using hn⟩
  · intro h
    obtain ⟨n,hn,he⟩ := h.exists_pow_eq'
    exact ⟨n, by simpa only [Equiv.Perm.coe_pow] using he⟩

theorem periodicOrbit_finset_symm65 {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α) (x : α) :
    (periodicOrbit (R.symm : α → α) x).toFinset = (periodicOrbit (R : α → α) x).toFinset := by
  ext y
  rw [periodicOrbit_finset_sameCycle65,periodicOrbit_finset_sameCycle65]
  exact Equiv.Perm.sameCycle_inv

theorem maximumCycleRoots_symm65 {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ) :
    Section5.maximumCycleRoots R.symm k = Section5.maximumCycleRoots R k := by
  classical
  ext v
  simp only [Section5.mem_maximumCycleRoots_iff,Section5.minimalPeriod_symm,
    periodicOrbit_finset_symm65]

theorem filtered_root_orbit_count_symm65 {n : ℕ} (R : Equiv.Perm (Fin n)) (k : ℕ)
    (P : Fin n → Finset (Fin n) → Prop) :
    (Finset.univ.filter (fun c : ↥(Section5.cycleOrbits R.symm k) =>
      P (Section5.cycleMaximum R.symm k c) c.val.toFinset)).card =
    (Finset.univ.filter (fun c : ↥(Section5.cycleOrbits R k) =>
      P (Section5.cycleMaximum R k c) c.val.toFinset)).card := by
  classical
  rw [filtered_cycle_count_eq_root_count R.symm k (fun v c => P v c.toFinset),
    filtered_cycle_count_eq_root_count R k (fun v c => P v c.toFinset),
    maximumCycleRoots_symm65]
  simp only [periodicOrbit_finset_symm65]

theorem spatialCycleCount_symm65 {n : ℕ} (R : Equiv.Perm (Fin n))
    (side : Corner) (k : ℕ) (a b : ℝ) :
    spatialCycleCount R.symm side k a b = spatialCycleCount R side k a b := by
  unfold spatialCycleCount
  convert filtered_root_orbit_count_symm65 R k
    (fun v _ => a < logLocation side v ∧ logLocation side v ≤ b) using 1 <;>
    congr 1 <;> ext c <;> simp

theorem excursionCycleCount_symm65 {n : ℕ} (R : Equiv.Perm (Fin n))
    (side : Corner) (k : ℕ) (a b δ : ℝ) :
    excursionCycleCount R.symm side k a b δ = excursionCycleCount R side k a b δ := by
  unfold excursionCycleCount
  convert filtered_root_orbit_count_symm65 R k
    (fun u S => a < logLocation side u ∧ logLocation side u ≤ b ∧
      ∃ v ∈ S, |Real.log (cornerDistance side v)-Real.log (cornerDistance side u)| > δ*Real.log n) using 1 <;>
    congr 1 <;> ext c <;> simp

end Luce.Section6
