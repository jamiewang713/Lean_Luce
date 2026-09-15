"""Package checked theorem statements and actual audit output for review."""
from pathlib import Path
import json

root = Path(__file__).resolve().parents[1]
raw = (root / "audit/section5-final-audit.log").read_bytes()
out = raw.decode("utf-16" if raw.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig").replace("\r\n", "\n")
validation = json.loads((root / "audit/section5-final-validation.json").read_text())
assert validation["axiom_reports"] == 18
assert all(not item["changed"] for item in validation["freeze"].values())

main_start = out.index("theorem Luce.section5_main_general.")
contract_start = out.index("def ShellMigrationContract.section5.", main_start)
check_start = out.index("theorem section5_contractCheck.", contract_start)
axiom_start = out.index("'Luce.section5_main_general' depends on axioms:", check_start)
pieces = {
    "section5-main-elaborated.txt": out[main_start:contract_start].split(" :=", 1)[0].rstrip() + "\n",
    "section5-contract-elaborated.txt": out[contract_start:check_start].rstrip() + "\n",
    "section5-contract-check-elaborated.txt": out[check_start:axiom_start].split(" :=", 1)[0].rstrip() + "\n",
}
for name, text in pieces.items():
    (root / "audit" / name).write_text(text, encoding="utf-8")

main_source = (root / "Luce/Section5ShellMain.lean").read_text(encoding="utf-8-sig")
main_type = main_source[main_source.index("theorem section5_main_general"):].split(" := by", 1)[0]
contract_source = (root / "Luce/Section5ShellContract.lean").read_text(encoding="utf-8-sig")
contract = contract_source[contract_source.index("def section5 : Prop :="):].split("\nend ShellMigrationContract", 1)[0].rstrip()
check_source = (root / "Luce/Section5ShellContractCheck.lean").read_text(encoding="utf-8-sig")
check = check_source[check_source.index("theorem section5_contractCheck"):].rstrip()
axioms = (root / "audit/section5-final-axioms.txt").read_text(encoding="utf-8")

report = f'''# Section 5 shell migration: completed proof and final audit

The full revised short-cycle theorem is proved as `Luce.section5_main_general`. The independently frozen, closed proposition is proved by `section5_contractCheck`, which has no external explicit, implicit, or instance parameters. The result includes full cyclic-density integrability, nonnegative intensities, convergence against every bounded continuous vector test, and joint total variation for every probability-space realization of the original finite Luce law.

## 1. Exact generalized theorem

The **exact fully elaborated type**, including universes and all instance arguments, is [section5-main-elaborated.txt](../audit/section5-main-elaborated.txt). It is copied directly from the successful Lean print output; only the suppressed proof body was removed. The complete print output and expanded assumption definitions are [section5-final-audit.log](../audit/section5-final-audit.log). The readable source type is:

```lean
{main_type}
```

Implementation: [Section5ShellMain.lean](../Luce/Section5ShellMain.lean). The Section 4 theorem remains `Luce.Shell.section4_main_poisson_general`; its exact type and source audit remain in [shell-migration-report.md](shell-migration-report.md) and [shell-statements-and-axioms.log](../audit/shell-statements-and-axioms.log). Both Section 4 theorem/check axioms were rechecked in the final combined audit.

## 2. Frozen closed contract and separate check

The contract below is the unchanged source in namespace `ShellMigrationContract`, with the imports and open namespaces shown in [Section5ShellContract.lean](../Luce/Section5ShellContract.lean). Its exact fully elaborated definition is [section5-contract-elaborated.txt](../audit/section5-contract-elaborated.txt).

```lean
{contract}
```

The actual completed proof, in a separate module importing the implementation and the frozen contract, is:

```lean
{check}
```

Its exact fully elaborated type is [section5-contract-check-elaborated.txt](../audit/section5-contract-check-elaborated.txt). The two local instance bindings come from the measurable-space and probability proofs universally quantified inside the contract. They are not external assumptions. `Luce/Sections1To7.lean` imports this check, so the default build checks it.

## 3. Assumption diff and recursive definition audit

```text
REMOVED: old uniform endpoint lower-bound assumption
ADDED: exact manuscript shell condition
OTHER MATHEMATICAL INPUT CHANGES: none
```

The source of truth is `fixed_points_shell_condition.tex`: finite Luce law at line 144, normalization at 217, profile assumption at 225–230, terminal shells/minima/raw shell limit at 254–279, and short-cycle intensities/conclusion at 335–354. The proposed migration plan supplied no additional allowed hypothesis.

`Weights n` contains only real rates and strict positivity for each of the n labels; it imposes no uniform lower or upper bound. `WeightArray` includes the empty row n=0. Normalization applies separately for n>0. `ProfileLimit` expands to Lebesgue measurability on (0,1), pointwise positivity there, and convergence of the actual step profiles in the extended L1 seminorm. Profile integrability is derived, not assumed. The full recursive type/meaning audit is [section5-shell-assumption-audit.md](section5-shell-assumption-audit.md), sharing the detailed original model audit in [shell-assumption-audit.md](shell-assumption-audit.md).

The raw endpoint predicate is exactly the iterated ENNReal limit of shell costs. The finite shells use real log(n/m), terminal depth n-label.val, and the minimum only for nonempty shells. Empty shells contribute zero. Finite support and both directions of the epsilon/eventually equivalence are proved. The old uniform predicate is preserved separately with its implication to the raw condition.

The limiting density, cycle counts, product intensity integrals, Poisson product law, and sup-over-events TV definition are unchanged. `cycleCountVector_raceDraw_eq_rank` proves the needed invariance under inverse permutations, and `cycleVectorTotalVariation_eq_countable` proves equality with the generic countable-space helper's TV convention. The existing profile-product/closed-cube integral identity is also proved. No representation was changed merely to make a proof easier.

Hash checks cover the original Section 4 snapshot (162 files), Section 5 snapshot (193 files), and intermediate cycle-shell contract (1 file). Every hash is unchanged, including manuscript, frozen definitions, toolchain, dependencies, and build configuration. The root module was extended to include the new contract check, as requested; existing targets and checking settings were not weakened.

## 4. Actual transitive axiom output

These are the actual final `#print axioms` results, including the main theorem, both main contract checks, and central endpoint/distributional results:

```text
{axioms.rstrip()}
```

Every report uses only `propext`, `Classical.choice`, and `Quot.sound`; the printed `.{{u}}` suffixes denote universe parameters. No `sorryAx`, project-specific axiom, or generated bypass axiom occurs in the transitive dependencies. This is a full dependency statement, not merely a claim that no new axiom was added.

## 5. Obligation ledger

The authoritative completed ledger is the **Final implementation ledger** at the top of [shell-obligation-ledger.md](shell-obligation-ledger.md). It links each shell/capacity/buffer/tightness, truncation, factorial-moment, intensity, point-probability, weak/TV, and law-transfer step to a completed proof and records where helper premises are discharged. Older progress entries are explicitly historical and superseded. No required mathematical estimate remains unresolved or is supplied as an extra input to the main theorem.

The final dependency sequence is: interior high/low truncation and cyclic local limits; retained shell estimates and full expectation tightness; exact factorial counting and all bulk joint moments; intensity integrability and cutoff convergence; finite point expansions with proved vanishing factorial remainder; spatial cutoff removal; countable-space TV and bounded tests; exact finite-law transport; closed contract check.

## 6. Commands actually run

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
# Exit 0: Build completed successfully (3893 jobs).
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5Final.lean
# Exit 0: fully elaborated theorem/contract/definition prints and 18 axiom reports.
python audit/validate_section5_final.py
# Exit 0: all 18 expected reports allowed; 162/193/1 frozen files unchanged;
# both main contract checks included in the default build.
```

Actual logs: [build](../audit/section5-final-build.log), [statements and axioms](../audit/section5-final-audit.log), [axioms only](../audit/section5-final-axioms.txt), [validation JSON](../audit/section5-final-validation.json). The build reports ordinary style/deprecation warnings; no errors or proof placeholders were used to obtain success.

## 7. Pre-existing gaps and semantic issues

The previously unfinished factorial-moment and joint-TV arguments are now resolved by the concrete proofs above. The historical global low-rate argument requiring uniform endpoint positivity was not used to prove the shell theorem. Its stronger-case results remain separate. No substantive error in the frozen contract or source contradiction was found, and no manuscript hypothesis or conclusion was altered. No required Section 4/5 migration gap remains.

The preserved conventions are explicit: paper label i is Lean label i-1, terminal depth is n-i+1, coordinate k counts cycles of length k+1, and Lebesgue measurability is represented by `NullMeasurable` on the profile domain. These are proved or previously audited representations, not additional restrictions.
'''
(root / "docs/section5-final-report.md").write_text(report, encoding="utf-8")
print("Wrote exact elaborated statement artifacts and docs/section5-final-report.md")
