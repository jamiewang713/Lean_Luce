import Luce.Section5CycleShellContract
import Luce.Section5CycleShellTightness

/-- Closed kernel-checked milestone; no parameters outside the contract. -/
theorem cycleShell_contractCheck : ShellMigrationContract.cycleShell := by
  intro w f hnorm hf hend L
  exact hend.cycle_shell_tightness hnorm hf L
