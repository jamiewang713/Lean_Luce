# Lemma 2.1: initial statement review (superseded)

The user has since resolved compactness to the literal open-cover meaning
and requested the direct proof. The full interface is now recorded in
`proposals/Section2PoissonCriterion.md`; the current proof and verification
record is `docs/predictable-poisson.md`. No additional separation or
metrizability hypothesis was adopted. The text below preserves the initial
review and its then-unresolved questions; it is not the current status.

The user has selected this lemma directly, deferring the separate Luce
compensator proposal. No new theorem has been proved or assumed in this
review. The spatial-space convention must be clarified before locking a
complete Lean signature. No extra topology, measurability, regularity, or
finiteness assumption has been committed to the production formalization.

## Exact source

`fixed_points.tex:589-603`, `lem:predictable-poisson`, with
`eq:poisson-criterion`:

```latex
\begin{lemma}\label{lem:predictable-poisson}
Let $I_{n,k}\in\{0,1\}$ be adapted, let $x_{n,k}$ be deterministic points in
a compact space $\mathsf X$, and let
$p_{n,k}=\E(I_{n,k}\mid\cF_{n,k-1})$.  Suppose that for a finite deterministic
measure $\nu$ on $\mathsf X$,
\begin{equation}\label{eq:poisson-criterion}
 \sum_kp_{n,k}\delta_{x_{n,k}}\Longrightarrow\nu
 \quad\text{in probability},
 \qquad
 \max_kp_{n,k}\longrightarrow0
 \quad\text{in probability}.
\end{equation}
Then $\sum_k I_{n,k}\delta_{x_{n,k}}$ converges to a Poisson random measure
with intensity $\nu$.
\end{lemma}
```

This is a general adapted-Bernoulli-array statement. No Luce weights,
permutations, exponential clocks, or independence of the indicators occur
in its hypotheses. Its proof can therefore be developed independently of
the unapproved Luce compensator theorem.

## Natural mathematical target

On each row's probability space, let I_(n,k) be adapted Bernoulli variables
and let p_(n,k) be their conditional means before the kth observation. For
deterministic points x_(n,k) of X, define

\[
A_n=\sum_k p_{n,k}\delta_{x_{n,k}},\qquad
\Xi_n=\sum_k I_{n,k}\delta_{x_{n,k}}.
\]

If A_n converges weakly in probability to the deterministic finite measure
nu, and the maximum individual coefficient p_(n,k) converges to zero in
probability, then Xi_n converges **in distribution as a random measure** to
a Poisson random measure with intensity nu.

The target is the full last sentence. Merely proving convergence of one
Laplace transform, or even leaving the Laplace-functional characterization
unproved, does not complete it.

## Variables, hypotheses, and conventions to review

- Row index n tends to infinity through natural numbers.
- The surrounding manuscript uses finite rows k = 1,...,n; the lemma's
  displayed sums omit the bounds. This is the intended candidate indexing
  for the full signature. An infinite-row interpretation must be stated
  separately and must not be replaced by finite rows without approval.
- Probability spaces and filtrations may vary with n. This does not require
  coupling the rows. Ordinary filtration inclusion/monotonicity are part of
  the filtration object, not new independence assumptions.
- Observations I_(n,k) are real-valued Bernoulli variables adapted to the
  row's filtration. An almost-sure Bernoulli formulation can be accommodated
  by choosing equivalent measurable zero-one versions; this must be proved.
- Conditional means are defined from the observations and history, not
  supplied as an independent law assumption. Their integrability and bounds
  follow from Bernoulli values and the probability measure.
- X is the same deterministic spatial space for every row. The manuscript
  says only "compact space." Its intended additional separation or
  metrizability conventions have not been specified.
- Spatial points x_(n,k) are deterministic and need not be distinct.
- nu is a deterministic finite nonnegative measure. Neither positive total
  mass nor a nonempty spatial space may be added merely to normalize it.
- The maximum concerns individual p_(n,k), not the merged mass A_n({x}) at
  a repeated spatial location. An empty finite maximum is taken as zero.
- There are no uniform constants in the theorem statement. The proof's
  auxiliary cap delta can be any fixed element of (0,1); K is chosen above
  nu(X)+1, independently of n. They are not extra assumptions in the target.
- No additional boundedness, integrability, tightness, or regularity
  assumptions may be propagated from auxiliary theorems into this target.

## Unresolved mathematical choice

The precise meaning of "compact space" controls the spatial Borel structure,
the measurable structure on the space of finite measures, and the final
weak convergence of their laws. The manuscript does not explicitly say
compact metric, compact Hausdorff, or finite Radon measure.

A compact metrizable space equipped with its Borel sigma algebra is a
sufficient familiar setting. It is **not** a consequence of the literal
`CompactSpace X` assumption in Lean, and may not be inserted as a mere
implementation convenience. Conversely, this review has not established
that metrizability is necessary or that the broader lemma is false.

For the full Lean statement, first determine which interpretation the
author intends. Then specify the weak topology and sigma algebra of the
random-measure state space, define the PRM law by its actual Poisson counts
and independence or by a proved equivalent construction, and make all
measurability obligations explicit. A Borel wrapper over the existing weak
finite-measure topology is one possible representation; it would still
require proved measurability and law-characterization bridges.

No complete Lean signature is claimed at this stage. In particular no
axiom or parameter standing for a missing PRM-convergence theorem is used.

## Pinned mathlib declarations inspected

The project remains pinned to Lean/mathlib v4.33.1.

- `MeasureTheory.FiniteMeasure`,
  `Mathlib.MeasureTheory.Measure.FiniteMeasure:117`, is the subtype of
  measures with finite total mass. Its measurable space at line 332 is
  inherited from the measure evaluation sigma algebra. Its weak topology
  is defined separately at line 505.
- `MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto`, same
  module at line 726, states that convergence in the weak topology is
  equivalent to convergence of integrals of every bounded continuous real
  test. It does not by itself identify the weak Borel sigma algebra with
  the existing evaluation sigma algebra.
- `MeasureTheory.TendstoInDistribution`,
  `Mathlib.MeasureTheory.Function.ConvergenceInDistribution:66`, includes
  a.e. measurability of the random variables and convergence of their laws
  in `ProbabilityMeasure E`. It supports varying row probability spaces
  and requires `OpensMeasurableSpace E` for the chosen state space E.
  Compactness of X alone does not supply this instance for the default
  weak topology and evaluation sigma algebra of `FiniteMeasure X` in the
  inspected pinned code. Such compatibility must not be assumed silently.
- `MeasureTheory.FiniteMeasure.ext_of_forall_integral_eq`,
  `Mathlib.MeasureTheory.Measure.FiniteMeasure:379`, obtains measure equality
  from equality of all bounded continuous test integrals under
  `HasOuterApproxClosed X` and `BorelSpace X`. Those extra premises must be
  derived or approved before this result is used.
- `isCompact_setOfPred_finiteMeasure_le_of_compactSpace`,
  `Mathlib.MeasureTheory.Measure.Prokhorov:70`, proves compactness of a
  bounded-total-mass set of finite measures on a compact Hausdorff Borel
  space. The Hausdorff premise must not be hidden in a dependency.
- `ProbabilityTheory.poissonMeasure (r : ℝ≥0) : Measure ℕ`,
  `Mathlib.Probability.Distributions.Poisson.Basic`, is the scalar Poisson
  law, including rate zero. In the same module,
  `ProbabilityTheory.poissonMeasure_real_singleton` states
  `(poissonMeasure r).real {j} = Real.exp (-r) * r ^ j / j.factorial`.
  This scalar law is not a supplied Poisson
  random-measure construction or a Laplace-functional convergence theorem.
  Searches of the pinned probability/measure-theory modules found no
  ready-made result giving the manuscript's full PRM conclusion.

## Existing proof components and remaining work

`Luce.BernoulliProcess.capped_laplace_tendsto_rows`,
`Luce/PredictablePoisson.lean:21`, proves the scalar Laplace limit with fixed
caps on total compensator mass and individual probabilities, for varying
row spaces. This is a reusable intermediate result, not the full lemma.

The existing `BernoulliProcess.stop`, `likelihood_martingale`,
`integral_likelihood`, and `likelihood_bounds_of_sum_le` provide the
dependent likelihood construction and a uniform pointwise bound. Thus a
faithful proof of the final lemma may use that bound in place of the
manuscript's displayed L2 route; doing so would not separately certify the
displayed L2 inequality as a formalized result.

The remaining scalar probability steps are:

1. Derive suitable measurable versions and extend finite rows by zero to
   reuse the existing natural-number-indexed process. Extra pointwise
   probability bounds in that structure must be derived by clipping a
   conditional-expectation version and proving almost-sure equality.
2. Derive convergence of total compensator mass and of the test
   `1 - exp(-g)` from the approved weak-convergence-in-probability hypothesis.
3. Prove that the union of the two cap-exceedance events has probability
   tending to zero, using `ConvergesInProbability.upper_tail`.
4. Apply existing deletion identities and
   `ConvergesInProbability.congr_off` to the stopped array, apply the capped
   theorem, and transfer the Laplace expectations back to the original
   array by bounding their difference by the deletion-event probability.
5. Construct the actual finite PRM law, including zero intensity, and prove
   the characterization that turns Laplace-functional convergence into
   the manuscript's full convergence-in-distribution conclusion.

The general lemma does not depend on first proving the Luce-specific
compensator proposition.

## STATEMENT AUDIT

- Target theorem: Lemma 2.1, not yet formalized or statement-locked.
- LaTeX source/label: `fixed_points.tex:589-603`, `lem:predictable-poisson`,
  `eq:poisson-criterion`.
- Approved statement changed: NO.
- Hypotheses added: NO.
- Hypotheses strengthened: NO.
- Conclusion weakened: NO.
- Quantifiers changed: NO.
- Constant dependencies changed: NO.
- Approved definitions mathematically changed: NO.
- Unresolved choice: intended compact spatial-space convention and the
  corresponding random-measure measurable/topological representation.

## TRUST AUDIT

- New axioms introduced: NO.
- New `sorry`/`admit`: NO; no new Lean proof body was written in this review.
- External assumptions used: NO.
- `#print axioms` result for Lemma 2.1: not available, since there is no
  asserted Lean theorem yet. No completed-proof claim is made.

## BUILD AUDIT

- Relevant new module checked: none; this stage changed documentation only.
- `lake build`: not rerun for documentation changes. The previously completed
  conditional-probability theorem retains its separate verified build/audit.
- Remaining obstacle: statement clarification, followed by the uncapping
  and full PRM-convergence proof obligations above.
