import Luce.Section6MaximumRootExpectation
import Luce.Section6EndpointExcursionProbability

noncomputable section
open Function
namespace Luce.Section6

/-- At a largest-label root, right depths can only increase. Thus leaving
the root interval is exactly crossing its upper depth boundary. -/
theorem maximum_root_right_escape_iff {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (v : Fin n) (hv : v ∈ Section5.maximumCycleRoots R k)
    {A B : ℝ} (hA : A ≤ (terminalDepth v : ℝ)) :
    (∃ z ∈ (periodicOrbit (R : Fin n → Fin n) v).toFinset,
      ¬ (A ≤ (terminalDepth z : ℝ) ∧ (terminalDepth z : ℝ) ≤ B)) ↔
    ∃ z ∈ (periodicOrbit (R : Fin n → Fin n) v).toFinset,
      B < (terminalDepth z : ℝ) := by
  have hmax := (Section5.mem_maximumCycleRoots_iff R k v).mp hv
  constructor
  · rintro ⟨z, hz, he⟩
    have hzv : z.val ≤ v.val := hmax.2 z hz
    have hd : terminalDepth v ≤ terminalDepth z := Nat.sub_le_sub_left hzv n
    have hdR : (terminalDepth v : ℝ) ≤ terminalDepth z := by exact_mod_cast hd
    exact ⟨z, hz, lt_of_not_ge (fun hB => he ⟨hA.trans hdR, hB⟩)⟩
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, fun h => (not_le_of_gt he) h.2⟩

/-- At a largest-label root, left depths can only decrease. Thus leaving
the root interval is exactly crossing its lower depth boundary. -/
theorem maximum_root_left_escape_iff {n : ℕ} (R : Equiv.Perm (Fin n))
    (k : ℕ) (v : Fin n) (hv : v ∈ Section5.maximumCycleRoots R k)
    {A B : ℝ} (hB : (v.val : ℝ)+1 ≤ B) :
    (∃ z ∈ (periodicOrbit (R : Fin n → Fin n) v).toFinset,
      ¬ (A ≤ (z.val : ℝ)+1 ∧ (z.val : ℝ)+1 ≤ B)) ↔
    ∃ z ∈ (periodicOrbit (R : Fin n → Fin n) v).toFinset,
      (z.val : ℝ)+1 < A := by
  have hmax := (Section5.mem_maximumCycleRoots_iff R k v).mp hv
  constructor
  · rintro ⟨z, hz, he⟩
    have hzv : z.val ≤ v.val := hmax.2 z hz
    have hzvR : (z.val : ℝ) ≤ v.val := by exact_mod_cast hzv
    exact ⟨z, hz, lt_of_not_ge (fun hA => he ⟨hA, by linarith⟩)⟩
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, fun h => (not_le_of_gt he) h.1⟩

end Luce.Section6
