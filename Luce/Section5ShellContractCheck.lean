import Luce.Section5ShellMain
import Luce.Section5ShellContract

theorem section5_contractCheck : ShellMigrationContract.section5 := by
  intro Ω mΩ P hP
  letI : ∀ n, MeasurableSpace (Ω n) := mΩ
  letI : ∀ n, MeasureTheory.IsProbabilityMeasure (P n) := hP
  intro w f hnorm hf hend π hπ hMass
  exact Luce.section5_main_general Ω P w f hnorm hf hend π hπ hMass
