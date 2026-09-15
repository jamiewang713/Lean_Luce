from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
def read_log(name):
    data = (root / "audit" / name).read_bytes()
    return data.decode("utf-16" if data.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig")

full = read_log("shell-lake-build.log")
milestone = read_log("shell-section4-milestone-build.log")
progress = read_log("section5-shell-progress.log")
assert "error:" not in full and "Build completed successfully" in full
assert "error:" not in milestone and "Build completed successfully" in milestone
assert "error:" not in progress
axioms = [line for line in progress.splitlines() if "depends on axioms:" in line]
assert len(axioms) == 6, len(axioms)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for line in axioms:
    assert set(re.search(r"\[([^]]*)\]", line).group(1).split(", ")) <= allowed, line
freeze = json.loads((root / "audit/shell-freeze-check.json").read_text())
assert freeze == {"checked_files": 162, "changed": []}
full_result = next(line for line in full.splitlines() if "Build completed successfully" in line)
milestone_result = next(line for line in milestone.splitlines() if "Build completed successfully" in line)
report = """# Actual shell migration validation

Commands ran in `D:\\princeton\\Research\\Lean\\Lean_luce` on the existing Lean 4.33.1 toolchain and pinned dependencies. No trusted dependency, checking option, or configured build target was changed.

## Section 4 milestone

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build Luce.ShellContractCheck
```

Exit code **0**. Actual final result: `""" + milestone_result + """`.
Complete log: `audit/shell-section4-milestone-build.log`.

## Default full build

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
```

Exit code **0**. Actual final result: `""" + full_result + """`.
Complete log: `audit/shell-lake-build.log`. `Luce.lean` includes the closed Section 4 contract-checking module and both new Section 5 progress modules. There are ordinary linter/deprecation warnings. The earlier foundation-only build also passed (3812 jobs), followed by the Section 4 default build (3826 jobs).

## Statement and transitive axiom audits

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/ShellMigrationStatements.lean
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5ShellProgress.lean
python audit/extract_shell_audit.py
```

All final runs exited **0**. The Section 4 audit prints the fully elaborated main theorem and frozen contract, the parameter-free contract check, recursive definitions, and 37 actual axiom reports. The Section 5 progress audit prints the exact compact low-rate and marked-edge statements and six axiom reports. Every reported dependency is among `propext`, `Classical.choice`, and `Quot.sound`.

Logs: `audit/shell-statements-and-axioms.log`, `audit/shell-axioms.txt`, and `audit/section5-shell-progress.log`. These certify the Section 4 main theorem and contract check; Section 5 has no completed main theorem or corresponding contract check.

One intermediate Section 5 audit invocation exited **1** because it ran while Lake was rebuilding its imported marked-edge object file. It was rerun after the build completed. Earlier proof-development iterations failed on explicit elaboration/tactic goals; all final production modules compile with those errors resolved. No failure was suppressed or converted into an assumption.

## Frozen semantic definitions

A Python SHA256 comparison against `audit/shell-contract-freeze.json` exited **0**, checking **162 files** with changed files `[]`. Machine-readable result: `audit/shell-freeze-check.json`. This covers the original closed contract, raw shell definitions, manuscript, pre-existing production definitions, and toolchain/dependency configuration. Only new proof modules and root imports were added outside that freeze.

The new finite-intensity constructor is checked against the literal raw measure in `section4_contractCheck` and against the historical constructor in `Luce.Shell.fullIntensity_eq_uniform`. Section 4 has no remaining assumption or axiom gap. The Section 5 cycle-shell and joint-convergence obligations remain explicitly unresolved in the ledger.
"""
(root / "audit/shell-build-results.md").write_text(report, encoding="utf-8")
print(full_result)
print("Section 5 progress: six transitive axiom reports, all allowed.")
