# Section 2 predictability: approved statement and completed proof

Source: `fixed_points.tex:569-579`, the definitions `eq:remaining-weight`,
`eq:predictable-p`, and the following unlabeled measurability assertion.

The source says:

> Both the numerator indicator and the denominator are
> $\cF_{n,k-1}$-measurable.

## Mathematical content

For an arbitrary permutation-valued map on a sample set, define
`F_m = σ(π(1),...,π(m))`. For deterministic positive weights, both

\[
\mathbf1\{\pi^{-1}(k)\ge k\},\qquad
W_k=\sum_{i=1}^n\theta_i\mathbf1\{\pi^{-1}(i)\ge k\}
\]

are `F_(k-1)`-measurable. This is a statement about information, so no
probability measure or particular permutation law is required.

The user approved the definition and complete statement in
`proposals/Section2Predictability.lean`. The production definitions and
theorem are `Luce.drawHistory` and `Luce.history_predictability`.

## Exact statement preservation

`audit/HistoryPredictability.lean` copies the approved history definition and
proposition. `approved_history` checks equality of the history definitions
by `rfl`; `approved_statement` proves the copied proposition directly using
the production theorem. Only namespaces differ.

All parameters are unchanged: arbitrary sample set `Ω : Type u`, row size
`n : ℕ`, positive deterministic weights `w : Weights n`, draw-order map
`π : Ω → Equiv.Perm (Fin n)`, and `k : Fin n`. The history contains `k.val`
draws, corresponding to the paper's position `k.val + 1`.

There are no added typeclass assumptions on `Ω`, no ambient sigma algebra,
no probability law, no assumed measurability of either quantity, no
integrability premise, no rate normalization, and no new constants. The
real codomain uses its standard Borel sigma algebra. The empty row has no
`k : Fin 0`; the first draw has the trivial preceding history.

## Proof and dependencies

- `DrawHistoryPermutation.lean`: a label remains precisely when none of the
  earlier draws selected it. This follows from permutation inversion and
  the order of the finite positions.
- `DrawHistory.lean`: exactly the approved join of pullback sigma algebras
  of the first observed coordinates, using the discrete finite label space.
- `HistoryPredictability.lean`: observed coordinates are measurable for this
  join. Availability is a finite intersection of events excluding an
  observed label. Its real indicator is measurable. Expanding the existing
  remaining-weight definition produces a finite sum of measurable terms.

The only local dependency outside these three modules is `Luce.Model`.
No probability theorem or unproved conditional-choice identity is used.

Pinned mathlib declarations used include `Measurable.of_comap_le`
(`Mathlib.MeasureTheory.MeasurableSpace.Basic`, the direction
`m₂.comap f ≤ m₁ → Measurable f`), `MeasurableSet.iInter`
(`Mathlib.MeasureTheory.MeasurableSpace.Defs`, a countable intersection of
measurable sets is measurable), `Measurable.ite` (Basic, measurable branches
with a measurable condition), and `Finset.measurable_sum`
(`Mathlib.MeasureTheory.Group.Arithmetic`, finite measurable summands give a
measurable sum). The intersection is finite in this application.

## STATEMENT AUDIT

- Target theorem: `Luce.history_predictability`.
- LaTeX source/labels: `fixed_points.tex:569-579`, `eq:remaining-weight`,
  `eq:predictable-p`, and the unlabeled measurability sentence.
- Statement changed: NO.
- Hypotheses added: NO.
- Hypotheses strengthened: NO.
- Conclusion weakened: NO.
- Quantifiers changed: NO.
- Constant dependencies changed: NO.
- Definitions mathematically changed: NO; the new production history is
  definitionally equal to the approved proposal.

## TRUST AUDIT

- New axioms introduced: NO.
- `sorry`/`admit` remaining in dependencies: NO.
- External assumptions used: NO.
- `#print` and `#print axioms` checked for all seven new production
  declarations and both statement-lock checks.
- Final theorem axioms: `[propext, Classical.choice, Quot.sound]`.
- The permutation helper uses `[propext, Quot.sound]`; every other axiom
  report contains the standard three axioms. No nonstandard axiom occurs.
- Source scan of all four local dependency modules found no prohibited proof
  tokens: `audit/history-predictability-source.txt`.
- An independent mathematical review found no statement or definition change.

## BUILD AUDIT

- `lake env lean Luce/HistoryPredictability.lean`: PASS, exit 0, no diagnostics.
- Default build inclusion: `Luce.lean` imports `Luce.HistoryPredictability`.
- `lake build`: PASS, exit 0, 3633 jobs.
- `lake env lean audit/HistoryPredictability.lean`: PASS, exit 0.
- The history definition has a class-definition reducibility warning; it is
  a sigma-algebra value rather than a typeclass instance. No mathematical or
  trust-changing option was added to suppress it.
- Remaining errors in the theorem and audit: none.
- Logs: `audit/history-predictability-module.txt`,
  `audit/history-predictability-build.txt`, `audit/history-predictability-print.txt`.

This approved statement is COMPLETE. The conditional probability identity
and the full Section 2 Poisson criterion remain separate unfinished targets.
