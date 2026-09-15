import Luce.Section5Reservoir
import Luce.Section5Cycles
import Luce.Section5FiniteInsertion
import Luce.Section5GhostCylinder
import Luce.Section5Predecessor
import Luce.Section5BulkCylinder
import Luce.Section5HighRates
import Luce.Section5ExceptionalHigh
import Luce.Section5DeletedRace
import Luce.Section5LowRates
import Luce.Section5CycleCutoff
import Luce.Section5Occupation
import Luce.Section5InteriorWindows
import Luce.Section5Lemma52
import Luce.Section5ExceptionalLow

/-!
# Section 5: the cyclic local lemma and further checked results

This entry point includes every new Section 5 proof module. The reservoir
lemma, finite insertion path lemma, ghost cylinder, added-predecessor bound,
and weighted bulk domination are proved, together with exact cycle-counting
factors and both halves of Proposition 5.4. Lemma 5.2's cyclic local law
is assembled in `Section5Lemma52`. The final joint Poisson limit is not
proved by this module. See `SECTION5_FORMALIZATION.md` for
the fixed source contract, proof coverage, and remaining obligations.
-/
