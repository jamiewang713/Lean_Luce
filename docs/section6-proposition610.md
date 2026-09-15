# Proposition 6.10: core factorial moments

The manuscript calls this result Proposition 6.10, with label
`prop:sp-factorial-moments`. The public statement is
`proposition610 : Proposition610Contract.proposition610`; the separate
checking module exposes `proposition610_contractCheck`.

The statement compares the actual mixed falling-factorial moment with
the product of the **exact** ideal category means. A category specifies
an active corner, a positive cycle length, and either the whole core or
a deterministic root interval. Intervals may depend on n. Categories
of the same corner and length have disjoint root windows. The actual
root is the largest label: its depth is a maximum on the left and a
minimum on the right. No asymptotic intensity replaces an ideal mean.

## Exact counting

`Section6CategoryCycleEquivalence` constructs the equivalence between
ordered lists of distinct category cycles with a selected root on each
cycle, and globally injective labelled block assignments. The number of
possible roots is the product of the cycle lengths. Cycle disjointness
follows from the permutation and from the category restrictions; eventual
disjointness of the two endpoint cores follows from the prescribed cutoffs.

`Section6CategoryFactorialExpectation` integrates the finite counting
identity against the actual exponential race. Integrability follows from
the finite permutation statistic. `Section6CategoryCoreActualSum` then
restricts each labelled vertex to its correct core and reindexes the
ordered category slots as a single finite cycle family. The rank-cylinder
event is preserved exactly, including mixed corners in one race.

`Section6CoreDepthEquivalence` proves that the actual largest-label root
becomes the stated depth root. `Section6CoreIdealCategorySum` identifies
each exact ideal mean with its restricted, distinct-vertex tuple sum.
`Section6CategoryCoreIdealSum` factors the unrestricted family sum and
restores precisely the same product of rotational divisors as in the
actual factorial moment.

## Quantitative comparison

The proof uses the already closed Proposition 6.5 local law and Lemma 6.4
domination matrix. It applies the collision argument from Lemma 6.9 to
matrices that may vary between cycles; this covers different ideal
corner kernels as well as the common actual domination matrix.

The removal of nonmoderate edges uses a direct weighted-path argument.
For an appropriate positive exponent k, set V(a)=a^(-k) on the left and
V(a)=a^k on the right. The proved weighted-row bounds become

    sum_b F(a,b) V(b) <= C V(a).

Cut the cycle at an arbitrary specified edge, bound that closing edge
by C/depth(target), and propagate V along the remaining open path.
Cyclic reindexing gives

    sum_cycles weight * V(source)/V(target) <= C^length * harmonic(core).

Failure of the local moderation condition forces this potential ratio
to be at least A^eta for a derived eta>0. Thus its contribution is bounded
by A^(-eta) times the usual logarithmic trace factor. This proves the
needed estimate directly for every edge, without selecting a vertex
of maximal logarithmic range. The argument applies to the full actual
domination matrix, including its exceptional terms, and to the ideal
kernels. No new weighted-row or probability assumption is introduced.

`PowerProfile.core_family_quantitative` combines three contributions:
nearby/overlapping labels, nonmoderate edges, and the local comparison on
the remaining family. The local law is used with all marked vertices
together. All deterministic category restrictions are kept on the good
set and dropped only in nonnegative upper bounds for errors.

Writing s for the total number of proposed cycles, the proof obtains

    |sum actual family weights - sum ideal family weights|
      <= C (1+log n)^(s+1) A_n^(-eta).

The prescribed rounded cutoffs are used literally. The proof derives
A_n tending to infinity, eventual nonemptiness and separation of the
cores, B_n <= n/A_n, and every endpoint cutoff required by the local law
and matrix estimates. A common positive eta is chosen across the finite
family, also when the family is empty. The rotational divisor is at least
one, so division preserves the final error bound. Thus the closed
contract holds with the explicit choice K=s+1.

## Scope and verification records

The proof covers an empty category list, zero factorial orders, one
cycle, fixed points, either active corner, mixed corners, whole cores,
root intervals, and both supported sampling grids. Nearby ranks and
overlapping assignments use the global domination estimate. No separation
or moderation premise survives in the closed proposition.

The dedicated audit inventory is `audit/section6-proposition610-manifest.json`.
It prints every new theorem type and its transitive axioms in
`audit/Section6Proposition610.lean`, as well as the complete contract and
category definitions. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. The full build, dedicated audit, regenerated whole-Section-6
audit, and hash results are recorded separately in
`audit/section6-proposition610-validation.json`.

The full build passed with 4412 jobs. All 87 theorem declarations in 38
new modules passed the dedicated audit. The unchanged whole-Section-6
generator obtained 1070 of 1075 reports: five existing declarations in
`TraceDensity68` were requested without that namespace. Its failed run
is retained. A separate namespace supplement checks those five actual
declarations without modifying the generator or hiding its errors.

The historical snapshots and existing checkers are preserved. The
manuscript changed outside this proof task after the new 17-file snapshot
was taken; that mismatch is retained and reported. This task did not edit
the manuscript. A temporary filename collision with
`Section6FiniteCommonConstants.lean` was repaired by restoring its exact
original hash; the new helpers instead live in
`Section6FactorialCommonConstants.lean`. Prior Proposition 6.5 proof
component hashes are checked again in the validation record.

This result proves the factorial-moment comparison. The subsequent CLTs
remain separate obligations.
