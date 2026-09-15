import Luce.Section6Lemma64Matrix
import Luce.Section6Lemma64Cycles

namespace Luce.Section6

/-- Full global domination and excursions, exactly as frozen before the
combined proof. Both components construct their estimates from the profile. -/
theorem lemma64 : Lemma64Contract.lemma64 := by
  exact ⟨lemma64_matrix, lemma64_cycles⟩

end Luce.Section6
