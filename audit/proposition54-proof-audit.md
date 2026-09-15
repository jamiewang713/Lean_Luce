# Proposition 5.4: separate proof audit

Result: PASS, 2026-09-11.

Executed successfully, each with exit code 0:

```powershell
lake build > audit/proposition54-full-build.log 2>&1
lake env lean audit/Section5Proposition54Proof.lean > audit/proposition54-proof-audit.log 2>&1
lake env lean audit/Section5Proposition54.lean > audit/proposition54-statement-types.log 2>&1
lake env lean audit/Section5.lean > audit/proposition54-section5-audit.log 2>&1
```

The full build completed **3794 jobs**, including all **47** Section 5
modules and the final `Luce` entry point. The complete local import closure
of Section 5 contains **88 modules**, recorded with SHA256 hashes in
`proposition54-full-local-dependencies.txt` and
`proposition54-full-source-hashes.txt`. All hashes were unchanged after
verification. Every Section 5 proof file is included in the default build.

The proof entry point checks the final proposition, the low-rate limit, and
the uniform bounded-cycle estimate. All three transitive axiom reports are:

```text
[propext, Classical.choice, Quot.sound]
```

The read-only environment walker independently inspects actual checked
declaration types and bodies, confirms the roots are theorem declarations,
and rejects extra axioms or unsafe/partial declarations. It visited
**46,029 transitive declarations**, including **359 local Luce declarations**,
with no prohibited dependency. It creates no mathematical declaration and
supplies no proof oracle. This check is more than a source-text search.

The focused type audit also prints twelve selected axiom reports, and the
aggregate Section 5 audit prints seventy-one. All sets were checked after
normalizing printed universe parameters: no extra axiom occurred.
`proposition54-axiom-summary.txt` records the counts. A supplementary source
scan of the complete local closure found zero admitted proofs or prohibited
trust mechanisms; its output is `proposition54-full-source-scan.log`.

Source-body inspection covered all four new modules and their interfaces
to the existing ghost-cylinder, row, expected-window, high-rate, and low-rate
profile theorems. The final proof discharges the length-integrability and
interior-index premises, proves the finite orbit charging inequality, and
derives the real limsup bounds. No assumed low-cycle estimate or local
unproved interface contributes to the final declaration.

Environment: Lean **4.33.1**, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. Exact output is in
`proposition54-environment.log`. Manuscript SHA256 remains
`0CDC05ACA34BD8E44A949747B815063F969BDD6A4963F650FF1E155B4C6E8E91`.
The manuscript and dependency-pin diff command returned no changes.
Existing style and deprecation warnings remain; the successful commands
have no errors. No proof source was changed after the final build and audits.

Statement fidelity was checked separately in
`proposition54-statement-audit.md`; a clean axiom report alone was not used
as evidence of correspondence with the manuscript.
