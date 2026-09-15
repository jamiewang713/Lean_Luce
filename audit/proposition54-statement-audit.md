# Proposition 5.4: separate statement audit

Result: PASS, 2026-09-11. This pass compares the actual elaborated types
and expanded definitions with `fixed_points.tex:1162–1240`, rather than
inferring correctness of the statement from its axiom report.

`lake env lean audit/Section5Proposition54.lean` exited 0. The output in
`proposition54-statement-types.log` exposes nine theorem types, seventeen
definitions/structures, and twelve axiom reports. The declaration inspected
is `Luce.section5_proposition54` in `Luce/Section5ExceptionalLow.lean`.

## Binder and definition comparison

- `w : WeightArray` contains exactly positive rates in every finite row.
  `NormalizedWeights w` is the standing mean-one normalization for positive
  rows. There is no extra bound on background rates.
- `ProfileLimit w f` is Lebesgue measurability on `(0,1)`, pointwise
  positivity there, and convergence of the actual step-profile error in
  the extended L1 seminorm. No smoothness, boundedness, or extra convergence
  assertion is hidden in this predicate.
- `EndpointAssumption w` has one positive gamma, one positive epsilon0,
  and a row threshold, followed by every row and label in the terminal
  neighborhood. In particular, it does not require epsilon0 less than one.
- `L : Nat` is arbitrary and includes zero. The two conclusions are the
  original iterated limits, with inner `limsup` over all original rows and
  outer filters `atTop` and `nhdsWithin 0 (Ioi 0)`, respectively.
- `highCycleExpectation` and `lowCycleExpectation` integrate the actual
  `shortCycleVertexCount` over `exponentialRace`. The filtered sets use
  the strict predicates `M < rate` and `rate < delta`; equality is excluded
  as in the paper. A vertex is counted once when its actual permutation
  orbit has length at most L. These are not counts of cycles, or counts
  of all vertices in a cycle that merely meets the filtered set.
- `raceRankPermutation` agrees almost surely with the rank permutation.
  Its tie extension is used only on the previously proved null set.
  One-based paper labels are `Fin n` values plus one throughout.

## Discharged proof restrictions

`OrbitAvoids R H v` quantifies over every vertex of the actual periodic
orbit of v. `boundedCycleEvent` restricts that orbit to rates at most M;
it does not restrict the background. The rooted tuple inherits this
condition by its proved iteration identity. The restricted vertex count
uses `minimalPeriod <= L`; positivity of finite permutation periods is
proved before translating it into the `Fin L` length index.

The finite row estimate drops distinctness, avoidance, and rate restrictions
only after establishing nonnegativity of every summand. The product is an
open path followed by its closing edge. The exact `Fin.consEquiv` bijection
supplies the path summation recurrence, with no lost factorial or rotation
factor. For k=0 the path product is one and the closing edge is the fixed
point event.

`ghostWindowVolume_ne_top_of_interior` proves the window has finite volume
before the real length is used. Its finite-index premise is derived
eventually from the bulk margin. The actual length is integrable by the
previous reservoir/occupation theorem. Nonnegative backgrounds and distinct
clocks are supplied almost surely by the actual exponential law.

The deterministic charging inequality is
`V(S) <= L * V(H) + V_avoiding(S,H)`. It follows from a subset of a finite
union of actual high-vertex orbits, whose cardinalities equal their minimal
periods. Overlap only increases the upper bound. It is valid even for
overlapping S and H and for L=0; disjointness is not assumed.

The endpoint hypothesis puts every sufficiently small-rate label below
`(1-epsilon0)n`. The proof chooses `alpha = 1-epsilon0/2` for the reservoir.
If that interval has no valid labels, the bulk implication proves this
without strengthening epsilon0's range. Constants precede all labels,
lengths through L, and eventual rows. The small-delta threshold is chosen
after the high-rate cutoff M; the row threshold is chosen after delta,
preserving the iterated-limit order.

Both vertex counts are integrable finite counts. For the outer limit,
eventual upper boundedness and a nonnegative lower bound are established
before using the real limsup. No totalized integral, division, or limsup
hides a missing finiteness condition.

## Nonvacuity, strategy, and scope

The existing checked `section5UnitWeights_assumptions` gives the constant-one
array satisfying normalization, profile, and endpoint assumptions together.
Thus the final assumptions are consistent and the theorem is not vacuous.

The implementation follows the source's high-rate comparison, interior
window estimate, row summation, orbit charging, and successive cutoff
argument. Finite orbit unions formalize the source's counting sentence;
explicit epsilon thresholds formalize its successive limits. No substantive
change of proof strategy or mathematical gap was identified for Proposition
5.4. No unresolved obligation remains for this proposition.

This audit does not claim Lemma 5.5 or Theorem 1.4 is proved. The separate
proof-integrity audit is recorded in `proposition54-proof-audit.md`.
