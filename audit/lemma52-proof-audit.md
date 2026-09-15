# Lemma 5.2 independent proof audit

Result: **PASS** on 2026-09-10. This is a proof-integrity audit, separate
from the source-to-statement audit. No mathematical source or proof module
was changed during this audit.

The final checked declarations are `Luce.section5_bounded_marked_asymptotic`,
`Luce.section5_cyclic_local`, and `Luce.section5_lemma52`. The last includes
the weighted cylinder bound for **every** row through
`Luce.ProfileLimit.weighted_bulk_cylinder_all`.

## Executed verification

From `D:\princeton\Research\Lean\Lean_luce`:

```powershell
lake env lean audit/Section5Lemma52Proof.lean *> audit/lemma52-proof-audit.log
lake env lean --version
git -C .lake/packages/mathlib rev-parse HEAD
```

The audit command exited **0**, with **0 errors**. Its complete output is
[lemma52-proof-audit.log](lemma52-proof-audit.log). It prints explicit
elaborated types for the three final theorems and nine selected branch
theorems, their final assembly proof terms, and **23** transitive axiom
reports. Every reported axiom set is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The audit additionally traverses the actual checked declaration types and
bodies, including opaque theorem bodies and inductive constructors. It
confirms the three final declarations are theorems and rejects any
additional axiom or unsafe/partial dependency. This independent traversal
reported **47,107 transitive declarations**, including **707 Luce
declarations**, with no prohibited dependency. The traversal only inspects
the existing environment; it introduces no theorem, axiom, or proof oracle.
Thus the result does not rely solely on a text search or on the cached
axiom lists.

Environment: Lean **4.33.1**, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. Exact output is preserved in
[lemma52-proof-environment.log](lemma52-proof-environment.log).
The separately executed project-wide `lake build` completed successfully
with **3790 jobs**, as recorded in [lemma52-full-build.log](lemma52-full-build.log).

## Source and dependency inspection

The recursive local import closure contains **72 modules**, listed in
[lemma52-local-dependencies.txt](lemma52-local-dependencies.txt).
[lemma52-proof-source-hashes.txt](lemma52-proof-source-hashes.txt) records
their SHA256 hashes; a post-audit comparison confirmed all 72 remained
unchanged. A supplementary scan of this complete closure for admitted
proofs, mathematical axioms, `native_decide`, unsafe code, and custom
elaboration/trust mechanisms found no matches (the expected `rg` exit 1);
the empty output is [lemma52-proof-source-scan.log](lemma52-proof-source-scan.log).

The substantive source-body review covered these dependencies:

- The actual normalized-gap law is derived by exponential disintegration,
  memorylessness, induction, relabelling, and summing all elimination
  orders. Independence is proved by a joint measure identity.
- Exponential mixed moments have separately proved integrability and exact
  factorial values. They transfer to actual deleted gaps by proved
  measure-preserving maps, including the first, second, and Taylor-envelope
  moments used by the expectation argument.
- The marked-rank insertion identity uses independent fresh coordinates
  and an exact resampling event identity. The passage from nonnegative
  extended integrals to real expectations has explicit measurable finite
  kernels and integrability proofs.
- The finite Taylor estimate proves a nonnegative pointwise error envelope
  before integrating it. The profile reservoir supplies the remaining-rate
  lower bound, and the proved mixed moments supply the expectation bound.
- The expectation transfer uses the proved second moment, without assuming
  independence between its coefficient and gap product. The final assembly
  discharges the sorted microscopic and cyclic-reduction premises.
- The cyclic analytic branch proves signed-integrand integrability, actual
  grid-cell integration, profile replacement, high-rate truncation, diagonal
  removal, and equality with closed-cube Lebesgue integration. The all-row
  cylinder extension explicitly handles positive denominators and empty
  row/tuple cases.

No unresolved proof obligation, admitted local interface, extra
mathematical axiom, or prohibited evaluation mechanism was found. This
conclusion concerns proof integrity; it does not replace the separate
comparison of theorem statements and definitions with the manuscript.
