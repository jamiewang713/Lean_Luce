"""Write the milestone report only after its actual Lean audit succeeds."""
from pathlib import Path

root = Path(__file__).resolve().parents[1]
axioms = (root / "audit/shell-axioms.txt").read_text(encoding="utf-8")
assert "'section4_contractCheck' depends on axioms: [propext, Classical.choice, Quot.sound]" in axioms
assert "'Luce.Shell.section4_main_poisson_general' depends on axioms:" in axioms
contract = (root / "Luce/ShellMigrationContract.lean").read_text(encoding="utf-8")
main = (root / "Luce/Section4ShellTheorem.lean").read_text(encoding="utf-8")
main = main[main.index("theorem section4_main_poisson_general"):].split(" :=", 1)[0]
check = (root / "Luce/ShellContractCheck.lean").read_text(encoding="utf-8")
check = check[check.index("theorem section4_contractCheck"):check.index("/-- The new constructor")].strip()
report = """# Shell migration report: Section 4 milestone

**Section 4 is proved and passes the frozen closed contract check. Section 5 remains incomplete.**

The generalized theorem is `Luce.Shell.section4_main_poisson_general`. It gives integrability of the literal diagonal density, the full spatial Poisson limit against every bounded continuous point-measure test, and scalar count total-variation convergence. It quantifies arbitrary row probability spaces and measurable permutations with the exact Luce masses. The old uniform-endpoint theorems remain available separately.

## Assumption diff for the proved Section 4 theorem

```text
REMOVED: old uniform endpoint lower-bound assumption
ADDED: exact manuscript shell condition
OTHER MATHEMATICAL INPUT CHANGES: none
```

The full assumption/type audit is `docs/shell-assumption-audit.md`. The closed contract and all definitions it originally imported remain byte-for-byte frozen. The new intensity constructor is proved equal to the historical constructor whenever the uniform condition holds (`Luce.Shell.fullIntensity_eq_uniform`); its equality with the raw measure required by the contract is definitional. Neither intensity finiteness nor tightness is a theorem input.

## Exact theorem statement

The following is the implementation's complete source statement, in namespace `Luce.Shell`. Its **fully elaborated** type, including every implicit and instance parameter, is printed in `audit/shell-statements-and-axioms.log`. That log also prints the expanded contract and recursively inspects the project definitions behind its predicates, law, counts, intensity, and convergence notions.

```lean
""" + main + "\n```\n"
report += "\n## Exact frozen closed contract\n\n```lean\n" + contract.strip() + "\n```\n"
report += "\n## Separate closed contract-checking theorem\n\n```lean\n" + check + "\n```\n"
report += """
The declaration has no external explicit, implicit, or instance parameters. It is outside any section carrying assumptions. Its complete proof calls the concrete shell theorem and supplies the exact finite intensity as a conclusion. `Luce.lean` imports this audit module, so it is checked by the default build.

## Obligation discharge and proof change

The detailed ledger is `docs/shell-obligation-ledger.md`. The shell proof now uses cutoff `j-sqrt(j)` and bounds each early shell contribution by `exp(1-sqrt(j))` for j at least 4096. This summable envelope follows from the sharp Jensen bound and the concrete block-capacity estimate. It avoids needing a separate distinct-maxima summation lemma and introduces no shell summability assumption: summability of this universal error was proved independently. The Q contribution is exactly the previously proved square-root buffered raw shell sum.

The spatial tail bridge retains the original rank/count definitions and handles the one-label offset with `alpha = 1-exp(-J)/2` for sufficiently large n. Expectation tightness is proved first; probability tightness follows by Markov. Interior expectation comparison and Fatou then yield finite full intensity. The existing interior convergence and terminal approximation arguments complete the spatial and scalar limits, with every endpoint premise discharged by these new proofs.

## Actual axiom output

The following lines are extracted verbatim from a successful Lean audit. The whitelist is exactly `propext`, `Classical.choice`, and `Quot.sound`. The shell main theorem and closed contract check are included, so this checks their full transitive dependencies, not merely newly written declarations.

```text
""" + axioms.strip() + "\n```\n"
report += """
## Build and remaining work

Actual commands, exit codes, and logs are recorded in `audit/shell-build-results.md`. The statement/axiom audit and frozen-definition comparison are separate checks; a successful compilation alone is not the basis for the claim above.

Section 5 is not certified by this milestone. Its revised compact low-rate truncation is now proved as `ProfileLimit.interior_low_rate_cycles_vanish`, using normalization and profile convergence alone. Its separate actual statement and axiom audit is `audit/section5-shell-progress.log`. Cycle-shell tightness and the subsequent joint theorem still require proofs. The closed Section 5 main-theorem contract is now frozen as ShellMigrationContract.section5; exact maximum-root counting and expectation identities are also proved. See docs/section5-rest-progress.md for the current remaining obligations. The historical global low-rate argument relies on the uniform endpoint hypothesis and cannot supply the new cycle-shell argument. The factorial-moment/joint Poisson/vector-TV completion was already unfinished. No Section 5 main-theorem completion or main-theorem axiom certificate is claimed.

No substantive error in the frozen Section 4 contract was discovered. The existing interpretation of measurable profile as Lebesgue measurable is preserved, as documented in the assumption audit. No model, probability law, count, density, or convergence definition was weakened.
"""
(root / "docs/shell-migration-report.md").write_text(report, encoding="utf-8")
print("Updated report from the verified contract, implementation, and actual axiom output.")
