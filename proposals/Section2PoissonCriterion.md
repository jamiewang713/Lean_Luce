# Lemma 2.1: full statement and representation

Source: `fixed_points.tex:589-603`, `lem:predictable-poisson`,
`eq:poisson-criterion`. The user selected the lemma directly and resolved
"compact" to the literal open-cover definition, then requested the proof.

For each n, let `(Ω n, P n)` be a probability space, with a filtration and
adapted Boolean observations indexed by `Fin n` (the manuscript's 1,...,n).
Write I for their real indicators and p for their conditional means before
each observation. For deterministic points x in the same compact X, put

    A_n = sum_k p_nk delta_(x_nk),   Xi_n = sum_k I_nk delta_(x_nk).

Assume A_n converges in probability to the deterministic finite measure nu
in the weak topology, and max_k p_nk converges in probability to zero.
Then the laws of Xi_n converge weakly to the finite Poisson random-measure
law of intensity nu.

## Exact proposed Lean interface

```lean
theorem predictable_poisson
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (B : ∀ n, FiniteAdaptedBernoulli (P n) n)
    (x : ∀ n, Fin n → X) (ν : FiniteMeasure X)
    (hweak : WeakMeasureConvergesInProbability P
      (fun n => (B n).predictableMeasure (x n)) ν)
    (hmax : ConvergesInProbability P
      (fun n => (B n).toProcess.rowMaximum n) 0)
    (F : FinitePointMeasure X →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F ((B n).pointMeasure (x n) ω) ∂P n)
      atTop (𝓝 (∫ μ, F μ ∂finitePoissonLaw ν))
```

The final F is universally quantified: the conclusion concerns every
bounded continuous function of the entire point measure, not just spatial
tests or Laplace functions.

## Hypotheses, variables, and constants

- X is a type with a topology, literal compactness, and its Borel sigma
  algebra. BorelSpace identifies the sigma algebra; it adds no separation
  or countability property to the topology.
- Each Ω n has an arbitrary sigma algebra and P n is a probability measure.
  Rows need not be on a common probability space or be mutually independent.
- B supplies only a filtration, Boolean observations, and adaptation.
  Real zero-one values, integrability, conditional means, predictability,
  and probability bounds are derived. Filtration time k+1 corresponds to
  manuscript time k for a zero-based Lean index.
- x is deterministic. Repeated points are allowed.
- nu is deterministic, nonnegative, and finite. Neither positive mass nor
  nonemptiness is assumed. The empty row has maximum zero.
- hweak and hmax are exactly the two convergence assumptions.
- F is an arbitrary bounded continuous real state test. Its measurability
  and integrability are proved, not assumed.
- There are no constants in the target. Auxiliary caps delta=1/2 and
  K=nu(X)+2 do not depend on n or on random outcomes. Compact cutoffs may
  depend on the desired error; they are proof choices, not hypotheses.

## Definitions and correspondence

`FinitePointMeasure X` is the subtype of actual finite measures expressible
as a finite sum of unit Dirac masses. Its topology is inherited from the
weak finite-measure topology, and its sigma algebra from measure evaluation.
The observed and predictable measures are the literal displayed sums.

The canonical conditional-probability representative is clipped into
[0,1]. A proved almost-everywhere equality to the original conditional
expectation shows this is a version choice, not a changed probability.

`WeakMeasureConvergesInProbability` quantifies over all weak-open
neighborhoods U of nu and requires P(A_n outside U) to tend to zero. It uses
the actual weak topology, rather than assuming a coordinate criterion.
For these finite arrays the neighborhood preimages are measurable.

`finitePoissonLaw nu` uses the standard finite-intensity generative
definition: N has Poisson distribution of mean nu(X); conditional on N=m,
take m iid points of law nu/nu(X), and sum their Dirac masses. When nu=0,
the law is the point mass at the zero measure. The construction is proved
to be a probability law, with Laplace functional

    exp(- integral_X (1-exp(-g)) dnu).

This representation uses the actual Poisson iid construction. The separate
equivalence theorem with independent Poisson counts on disjoint measurable
sets is not asserted as a formalized result by this statement.

There is no Hausdorff, metric, second-countability, Radon, tightness,
expected-count bound, or weak-Borel/evaluation-sigma identification in the
interface. Literal compactness is used to prove compactness of the sets of
point measures with count at most N. Laplace algebra approximation then
proves convergence for all the state tests F above.

## Proof correspondence

Follow the manuscript's predictable deletion, likelihood normalization,
product approximation, and removal of deletion. For the likelihood error,
the proof uses a stronger uniform pointwise bound. The manuscript's uniform
L2 conclusion is also proved separately from that bound; the assembled
limit proof does not invoke the separate L2 theorem. Total
mass and tested compensator convergence follow from hweak. Derive count
tightness using the same deletion and Markov's inequality. Finally complete
the manuscript's last Laplace-functional implication with compact-set
approximation on the actual point-measure space.

This file records the signature before the main proof is assembled.
