# Actual shell migration validation

Commands ran in `D:\princeton\Research\Lean\Lean_luce` on the existing Lean 4.33.1 toolchain and pinned dependencies. No trusted dependency, checking option, or configured build target was changed.

## Section 4 milestone

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build Luce.Section4ShellContractCheck
```

Exit code **0**. Actual final result: `Build completed successfully (3765 jobs).`.
Complete log: `audit/shell-section4-milestone-build.log`.

## Default full build

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" build
```

Exit code **0**. Actual final result: `Build completed successfully (3828 jobs).`.
Complete log: `audit/shell-lake-build.log`. `Luce/Sections1To7.lean` includes the closed Section 4 contract-checking module and both new Section 5 progress modules. There are ordinary linter/deprecation warnings. The earlier foundation-only build also passed (3812 jobs), followed by the Section 4 default build (3826 jobs).

## Statement and transitive axiom audits

```powershell
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section4ShellMigrationStatements.lean
& "$env:USERPROFILE/.elan/bin/lake.exe" env lean audit/Section5ShellProgress.lean
python audit/extract_shell_audit.py
```

All final runs exited **0**. The Section 4 audit prints the fully elaborated main theorem and frozen contract, the parameter-free contract check, recursive definitions, and 37 actual axiom reports. The Section 5 progress audit prints the exact compact low-rate and marked-edge statements and six axiom reports. Every reported dependency is among `propext`, `Classical.choice`, and `Quot.sound`.

Logs: `audit/shell-statements-and-axioms.log`, `audit/shell-axioms.txt`, and `audit/section5-shell-progress.log`. These certify the Section 4 main theorem and contract check; Section 5 has no completed main theorem or corresponding contract check.

One intermediate Section 5 audit invocation exited **1** because it ran while Lake was rebuilding its imported marked-edge object file. It was rerun after the build completed. Earlier proof-development iterations failed on explicit elaboration/tactic goals; all final production modules compile with those errors resolved. No failure was suppressed or converted into an assumption.

## Frozen semantic definitions

A Python SHA256 comparison against `audit/shell-contract-freeze.json` exited **0**, checking **162 files** with changed files `[]`. Machine-readable result: `audit/shell-freeze-check.json`. This covers the original closed contract, raw shell definitions, manuscript, pre-existing production definitions, and toolchain/dependency configuration. Only new proof modules and root imports were added outside that freeze.

The new finite-intensity constructor is checked against the literal raw measure in `section4_contractCheck` and against the historical constructor in `Luce.Shell.fullIntensity_eq_uniform`. Section 4 has no remaining assumption or axiom gap. The Section 5 cycle-shell and joint-convergence obligations remain explicitly unresolved in the ledger.
