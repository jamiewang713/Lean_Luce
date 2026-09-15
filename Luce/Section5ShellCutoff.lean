import Luce.Section5LateShellGeometry
import Luce.Section4EndpointShellCover

noncomputable section
namespace Luce

/-- The unique logarithmic shell number, also defined for the interior
shell zero. It does not change the manuscript's positive-shell convention. -/
def terminalShellNumber {n : ℕ} (v : Fin n) : ℕ :=
  ⌊Real.log ((n : ℝ) / (terminalDepth v : ℝ))⌋₊

def terminalShellTime {n : ℕ} (v : Fin n) : ℝ :=
  (terminalShellNumber v : ℝ) - Real.sqrt (terminalShellNumber v)

theorem terminalShellNumber_eq_of_mem {n j : ℕ} {v : Fin n}
    (hv : v ∈ terminalShell n j) : terminalShellNumber v = j := by
  apply (Nat.floor_eq_iff ((Nat.cast_nonneg j).trans (mem_terminalShell.mp hv).2.1)).mpr
  exact (mem_terminalShell.mp hv).2

theorem mem_terminalShellNumber {n : ℕ} (v : Fin n) (hv : 1 ≤ terminalShellNumber v) :
    v ∈ terminalShell n (terminalShellNumber v) := by
  have hlog : 0 ≤ Real.log ((n : ℝ) / (terminalDepth v : ℝ)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by exact_mod_cast terminalDepth_pos v)).mpr
    simpa using (show (terminalDepth v : ℝ) ≤ n by exact_mod_cast terminalDepth_le v)
  exact mem_terminalShell.mpr ⟨hv, Nat.floor_le hlog, Nat.lt_floor_add_one _⟩

theorem source_shell_time_le_target {n r : ℕ} {u v : Fin n}
    (hu : u ∈ terminalShell n r) (hv : 1 ≤ terminalShellNumber v) (huv : u < v) :
    (r : ℝ) - Real.sqrt r ≤ terminalShellTime v :=
  predecessor_shell_buffer_le hu (mem_terminalShellNumber v hv) huv

theorem cutoff_le_terminalShellTime {n J : ℕ} {v : Fin n}
    (hJ : 1 ≤ J) (hv : J ≤ terminalShellNumber v) :
    (J : ℝ) - Real.sqrt J ≤ terminalShellTime v :=
  shell_buffer_time_mono (by exact_mod_cast hJ) (by exact_mod_cast hv)

end Luce
