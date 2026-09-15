# Tail tightness: approved statement and completed proof

Source: `fixed_points.tex:930`, equation `eq:tail-tightness`.
Production theorem: `Luce.tail_fixed_point_tightness` in
`Luce/TailTightness.lean:40`. Imported by the default `Luce` target.

## Mathematical statement

Let the positive triangular array satisfy mean-one normalization and the
approved uniform endpoint Assumption 1.2. For each row let its clocks be
independent exponentials with the given rates, on any probability space.
Write

\[
T_n(\alpha)=\#\{1\le k\le n:\alpha n<k,\ R_{n,k}=k\}.
\]

Then

\[
\lim_{\alpha\uparrow1}\limsup_{n\to\infty}P_n(T_n(\alpha)>0)=0.
\]

This is the approved direct-count formulation. An eventual definition of
the full random measure must be connected to this count by exact equality.
This theorem does not claim that the full random-measure convergence has
been formalized.

## Statement lock

`proposals/Section4TailTightness.lean` retains the approved definition and
complete proposition. `audit/TailTightness.lean` reproduces both and checks:

- Equality of the approved and production count definitions by `rfl`.
- The approved full proposition is proved directly by the production theorem.

All variables and hypotheses are preserved: arbitrary row spaces `Ω n`, their
measurable spaces and probability measures `P n`, the positive array `w`,
`NormalizedWeights w`, `EndpointAssumption w`, clocks `E n i`, their marginal
`HasLaw` hypotheses, and independence within each row. The row spaces can
vary. There is no assumption relating different rows.

The conclusion has no new constant. The endpoint witnesses depend on the
array, uniformly in row and label. The proof retains their rate lower bound
γ and chooses a smaller neighborhood internally. No profile convergence,
integrability, stronger clock measurability, completeness, or no-ties
hypothesis is added. Row zero is empty and does not affect the limsup.

## Proof and dependencies

1. `TailCountIndex.lean` proves exact equality between the spatial count and
   the terminal count with `ceil (ε*n)` labels, including integer boundaries.
2. `TailProbability.lean` proves measurability, the count bound by `n`, and
   integrability, then applies Markov at threshold 1. Joint-law transfer uses
   the marginal exponential laws and within-row independence.
3. `TailAssumptions.lean` derives the normalization and terminal-rate
   hypotheses required by the existing endpoint estimates. It proves both
   eventual boundedness of expectations and the bound
   `2^(1+γ/2) * ε^(γ/4)` for sufficiently small positive ε.
4. `TailTightness.lean` compares the probability and expectation limsups,
   explicitly discharging boundedness obligations, and removes the row shift.
5. `TailLimit.lean` applies the power envelope as `α` approaches 1 from below.

Pinned mathlib declarations used:

- `ProbabilityTheory.iIndepFun.hasLaw_pi`, `Mathlib.Probability.HasLaw`:
  independent finite coordinates with specified marginal laws have the
  corresponding product joint law.
- `ProbabilityTheory.HasLaw.measureReal_eq`, the same module: measurable
  events have the same real probability after transfer by the specified law.
- `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`,
  `Mathlib.MeasureTheory.Integral.Bochner.Basic`: for integrable,
  a.e.-nonnegative real `f`, `ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ`.
- `Filter.limsup_le_limsup`, `Mathlib.Order.LiminfLimsup`: eventual comparison
  implies limsup comparison with the stated coboundedness/boundedness premises.
- `Filter.limsup_nat_add`, the same module:
  `limsup (fun i => f (i+k)) atTop = limsup f atTop`.

## STATEMENT AUDIT

- Target theorem: `Luce.tail_fixed_point_tightness`.
- LaTeX source/label: `fixed_points.tex:930`, `eq:tail-tightness`.
- Statement changed: NO.
- Hypotheses added: NO.
- Hypotheses strengthened: NO.
- Conclusion weakened: NO.
- Quantifiers changed: NO.
- Constant dependencies changed: NO.
- Definitions mathematically changed: NO; production count matches the
  approved definition by definitional equality.

## TRUST AUDIT

- New axioms introduced: NO.
- `sorry`/`admit` remaining in dependencies: NO.
- External assumptions used: NO.
- `#print` and `#print axioms`: checked for the final theorem and all new
  helper declarations, plus important existing dependencies.
- All 23 axiom reports in `audit/tail-tightness-print.txt` contain exactly
  `[propext, Classical.choice, Quot.sound]`; no nonstandard axioms.
- Recursive source search covered 22 local dependency modules and found no
  prohibited proof tokens. See `audit/tail-tightness-source-audit.txt` and
  `audit/tail-tightness-local-dependencies.txt`.
- An independent read-only mathematical review found no change of target or
  hidden additional assumption.

## BUILD AUDIT

- `lake env lean Luce/TailTightness.lean`: PASS, exit 0.
- Included in the default library build: YES.
- `lake build`: PASS, exit 0, 3628 jobs.
- `lake env lean audit/TailTightness.lean`: PASS, exit 0; two harmless unused
  instance-name warnings in the copied approved proposition.
- Remaining errors: none in the checked theorem and audit.
- Logs: `audit/tail-tightness-module.txt`, `audit/tail-tightness-build.txt`,
  and `audit/tail-tightness-print.txt`.

The approved tail-tightness theorem is complete. Section 4 as a whole remains
incomplete; see `docs/section4-status.md` for its other obligations.
