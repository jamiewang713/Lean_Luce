# Section 2: scope, existing coverage, and next statement

Current objective: formalize **all of Section 2**, “Predictable fixed-point
probabilities,” `fixed_points.tex:562-660`. The earlier Section 4 work is
preserved. Its completion is not substituted for the current objective.

The approved history definition and predictability theorem are now complete:
`Luce.drawHistory` and `Luce.history_predictability`. See
`docs/history-predictability.md` for the exact statement lock and current
build/trust audit. The approved conditional-probability theorem is also
complete: `Luce.predictable_fixed_point_probability`. Its full Luce masses,
prefix identities, conditional-expectation proof, and statement lock are
audited in `docs/predictable-probability.md`. The user has now selected
**Lemma 2.1 directly**, `lem:predictable-poisson`, and this theorem is now
COMPLETE for its recorded statement, with module/build/axiom checks passed.
The spatial-space convention is now resolved to literal open-cover
compactness. The exact full interface is recorded in
`proposals/Section2PoissonCriterion.md`, and the current proof/build record
is `docs/predictable-poisson.md`. The earlier initial review is preserved in
`docs/section2-poisson-statement-review.md` as historical context.

The random-measure compensator, `eq:compensator-measure`, is deferred.
Its proposed definitions, full Lean statement, and representation choices are recorded in
`docs/section2-compensator-proposal.md` and `proposals/Section2Compensator.lean`.
That proposition is awaiting approval and has not been proved.

## Required coverage

| Source item | Existing evidence | Remaining obligation |
| --- | --- | --- |
| Draw history, line 569 | Approved `Luce.drawHistory` in `DrawHistory.lean` | Definition complete; relate to a filtration wrapper where needed later. |
| `eq:remaining-weight`, line 571 | `remaining` and `Weights.total` in `Model.lean`; `measurable_remaining_weight` in `HistoryPredictability.lean` expands the exact indicator sum | Approved measurability complete; exact denominator used in the conditional-probability theorem. |
| `eq:predictable-p`, line 575 | Approved `Luce.predictable_fixed_point_probability`, derived from the full product law using proved prefix-mass identities | COMPLETE for the approved statement on an arbitrary probability space. |
| Measurability assertion, line 579 | `Luce.history_predictability`, with an audited equality to the approved statement | COMPLETE for the approved statement. |
| `eq:compensator-measure`, line 581 | Generic scalar Bernoulli compensator sums exist; exact finite-measure and tested-martingale statement proposed in `Section2Compensator.lean` | Deferred while the user prioritizes Lemma 2.1; proposal remains unapproved. |
| `lem:predictable-poisson`, line 589; `eq:poisson-criterion`, line 594 | `Luce.predictable_poisson` in `PoissonCriterion.lean`; full weak-law conclusion on literal compact spaces | COMPLETE; combined build/trust result is recorded in `docs/predictable-poisson.md`. |
| Recursive predictable deletion, lines 609-615 | `stoppedMass`, `keepTerm`, `stoppedProbability`, their bounds and measurability; `BernoulliProcess.stop` | Connected through `FiniteAdaptedBernoulli` and `UncappedPoisson`; conditional-mean version equality is proved. |
| `eq:likelihood-martingale`, line 618 | `BernoulliProcess.likelihood_martingale`, `integral_likelihood` | Used in the capped likelihood comparison and full uncapping proof. |
| Single-factor second moment, lines 630-633 | Algebraic second-moment formula and exponential bound in `Predictable.lean` | Package the conditional second-moment identity and the iterated estimate if certifying this displayed proof assertion. |
| `eq:likelihood-L2`, line 636 | `integral_likelihood_sq_le`, `stopped_integral_likelihood_sq_le` | Uniform bound proved with C_(g,delta)=1/(1-delta); the main comparison uses the stronger pointwise bound. |
| Product approximation, lines 642-646 | `product_poisson_error_of_atom_bound` and capped integral-error estimate | Applied in the uncapped proof after deriving the good-event probabilities. |
| Deletion probability vanishes, lines 648-650 | `row_bad_event_tendsto_zero`, `uncapped_laplace_tendsto_rows` | Proved from the two convergence hypotheses. |
| Final Laplace functional and PRM conclusion, lines 652-659 | `pointMeasure_laplace_tendsto`, `finitePoissonLaw`, `pointMeasure_law_convergence_of_laplace`, `predictable_poisson` | Full bounded-continuous-state-test convergence; standard finite Poisson iid generative definition. The separate disjoint-count characterization is not claimed as an additional formalized theorem. |

## Earlier capped intermediate result: exact limitations

The following records the scope of the earlier helper, not the scope of
the now-assembled full `predictable_poisson` theorem. All its extra caps
are derived by the new uncapping proof.

`Luce.BernoulliProcess.capped_laplace_tendsto_rows` in
`Luce/PredictablePoisson.lean:21` allows row-dependent probability spaces.
It assumes a fixed cap `δ < 1`, a deterministic total cap `K`, a measurable
random upper bound `a_n` with `0 ≤ a_n ≤ δ` pointwise, and
`p_nk ≤ a_n` for every index, including indices beyond the finite row length.
It also assumes convergence in probability of `a_n` to zero and of one
weighted compensator to a nonnegative scalar `lam`.

Its conclusion is convergence of one expected exponential to `exp (-lam)`.
These hypotheses and conclusion are useful intermediate mathematics, not
the full statement of `lem:predictable-poisson`. All extra intermediate
hypotheses must be derived before using this theorem for that lemma.

The existing `BernoulliProcess` structure uses pointwise zero-one values and
probabilities in `[0,1]`, predictable measurable versions, and an a.e.
conditional-mean identity. `FiniteAdaptedBernoulli` now derives these fields
from adapted Boolean observations; clipping the conditional means is proved
to preserve them almost everywhere.

The lemma permits repeated spatial locations. Its maximum condition concerns
the individual coefficients `p_(n,k)`, not the mass at a spatial point after
merging coincident locations. No distinctness assumption may be introduced.

## Approved and completed statement: measurability before the draw

Exact source sentence, `fixed_points.tex:579`:

> Both the numerator indicator and the denominator are
> $\cF_{n,k-1}$-measurable.

Associated labels: `eq:remaining-weight`, `eq:predictable-p`. The sentence
itself has no separate LaTeX label.

For a map `π` from an arbitrary sample set into permutations of `1,...,n`, put

\[
\mathcal F_m=\sigma(\pi(1),\ldots,\pi(m)).
\]

The proposed theorem says that, for every `1 ≤ k ≤ n`, both

\[
\mathbf1\{\pi^{-1}(k)\ge k\},\qquad
W_k=\sum_{i=1}^n\theta_i\mathbf1\{\pi^{-1}(i)\ge k\}
\]

are `F_(k-1)`-measurable. The weights are deterministic and positive, as in
the existing model. This statement is about which information determines
these quantities; no probability law is needed for this measurability fact.

### Proposed Lean definition

`proposals/Section2Predictability.lean` contains the complete proposal:

```lean
def drawHistory {Ω : Type u} {n : ℕ}
    (π : Ω → Equiv.Perm (Fin n)) (m : ℕ) : MeasurableSpace Ω :=
  ⨆ j : Fin n, ⨆ (_ : j.val < m),
    MeasurableSpace.comap (fun ω => π ω j) ⊤
```

The label sigma algebra `⊤` is the discrete sigma algebra on the finite label
set. `comap` gives the sigma algebra generated by one draw; the supremum
generates the history from precisely the first `m` draws. It uses the actual
uncompleted history, without adding null sets or future observations.

### Proposed Lean statement

```lean
∀ {Ω : Type u} {n : ℕ} (w : Weights n)
  (π : Ω → Equiv.Perm (Fin n)) (k : Fin n),
  Measurable[drawHistory π k.val]
    (fun ω => if k ≤ (π ω).symm k then (1 : ℝ) else 0) ∧
  Measurable[drawHistory π k.val]
    (fun ω => w.total (remaining (π ω) k))
```

Line-by-line correspondence and complete variable/assumption inventory:

| Lean component | Meaning |
| --- | --- |
| `Ω : Type u` | Arbitrary sample set; universe level is an implementation parameter. |
| `n : ℕ` | Row size. There is no `n > 0` hypothesis: a chosen `k : Fin n` already entails a nonempty row. |
| `w : Weights n` | Every deterministic rate `w.rate i` is strictly positive, as encoded by the approved model. No normalization is needed here. |
| `π : Ω → Equiv.Perm (Fin n)` | The permutation in draw order; bijectivity is built into the permutation type. |
| `k : Fin n` | Paper label and draw position `k.val + 1`. |
| `drawHistory π k.val` | Exactly `F_(k-1)` in the paper's one-based notation. |
| `k ≤ (π ω).symm k` | The one-based rank of label `k` is at least its draw position. Shifting both sides by one preserves the comparison. |
| Real `if ... then 1 else 0` | The paper's availability indicator. |
| `w.total (remaining (π ω) k)` | The same remaining-weight sum as in `eq:remaining-weight`; uses the existing, unchanged definitions. |
| `Measurable[...] ... ∧ Measurable[...] ...` | Both quantities are measurable for the same pre-draw history. |

There are no additional typeclass assumptions on `Ω`, no assumed
measurability of these quantities, no integrability hypotheses, no new
finiteness assumptions beyond the paper's finite permutation, and no new
constants. The real codomain uses its standard Borel sigma algebra.

Differences requiring explicit review: zero-based implementation indices;
writing the generated sigma algebra as a supremum of pullbacks; and isolating
the law-independent measurability assertion from the subsequent probabilistic
identity. This does not establish or assume that `predictableChance` is the
conditional probability. Existing definitions are not changed.

This lemma supplies the exact pre-draw measurability needed by the conditional
probability calculation. Its deterministic dependency is that a label remains
precisely when it has not appeared in any earlier draw. The approved proof and
all its dependencies have now passed the checks in `docs/history-predictability.md`.

### Pinned mathlib dependencies inspected

- `comap_measurable`, `Mathlib.MeasureTheory.MeasurableSpace.Basic`:
  `Measurable[m.comap f] f` for any function `f` into a measurable space.
- `measurable_iff_comap_le`, the same module:
  `Measurable f ↔ m₂.comap f ≤ m₁`.
- `Measurable.ite`, the same module: measurable branches and a measurable
  condition set give a measurable piecewise function.
- `Finset.measurable_sum`, `Mathlib.MeasureTheory.Group.Arithmetic`:
  measurability of each summand implies measurability of the finite sum
  (generated by `to_additive` from `Finset.measurable_prod`).

## Choices pending for the full Poisson lemma

The manuscript says only “compact space.” It does not explicitly specify
Hausdorff, metrizable, Polish, or Radon assumptions. None may be silently
added. The intended measurable structure, finite-measure weak topology,
meaning of convergence in probability for random measures on varying row
spaces, row-index range, and representation of a Poisson random measure need
a separate proposal before proving the full lemma.

Pinned mathlib has finite-measure weak topology, generic convergence tools,
and the scalar Poisson law. The inspected finite-measure measurable structure
uses evaluations; it must not silently be identified with the Borel sigma
algebra of the weak topology at this generality. Searches did not locate an
existing PRM/Laplace-functional convergence theorem. These are explicit
remaining obligations, not external assumptions.

## Historical verification before predictability approval

The production change in this stage is the default import of the existing
`Luce.PredictablePoisson` module. No mathematical definition, signature, or
proof body was altered. The proposal only defines a proposition and does not
assert it. Verification logs are under `audit/section2-*`.

### STATEMENT AUDIT

- Target: first missing predictability assertion; full goal remains Section 2.
- Source/labels: `fixed_points.tex:569-579`, `eq:remaining-weight`,
  `eq:predictable-p`, and the unlabeled measurability sentence.
- Approved statement changed: NO.
- Hypotheses added: NO.
- Hypotheses strengthened: NO.
- Conclusion weakened: NO.
- Quantifiers changed: NO.
- Constant dependencies changed: NO.
- Definitions mathematically changed: NO; new history definition is a proposal.
- At this earlier stage no new proof existed. The user subsequently approved
  this statement and it is now complete; see `docs/history-predictability.md`.

### TRUST AUDIT

- New axioms introduced: NO.
- External assumptions used: NO.
- Source scan of inspected model/likelihood/stopping/convergence modules:
  no prohibited proof tokens found.
- Printed declaration and axiom checks: `audit/Section2Existing.lean`.
- All 18 printed axiom reports passed and contain exactly
  `[propext, Classical.choice, Quot.sound]`. No nonstandard axioms or
  `sorryAx` occur in these checked dependency chains.
- New proposal is unproved, not an assumed theorem.

### BUILD AUDIT

- Default `lake build`: PASS, 3630 jobs.
- Proposal type-check: PASS; one class-definition reducibility warning,
  unrelated to mathematical content. This is not a theorem proof.
- `lake env lean Luce/PredictablePoisson.lean`: PASS, exit 0.
- `lake env lean audit/Section2Existing.lean`: PASS, exit 0.
- Remaining errors in checked files: none.
- Section 2: NOT COMPLETE.
