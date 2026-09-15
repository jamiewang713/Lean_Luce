import Luce.Section6Lemma64Contract
import Luce.Section6Lemma64Cycles

namespace Luce.Section6

/-- Separate closed check for the complete cycle-count portion only.
The full matrix-and-cycles contract remains a separate obligation. -/
theorem lemma64_cycles_contractCheck : Lemma64Contract.cycles := by
  exact lemma64_cycles

end Luce.Section6
