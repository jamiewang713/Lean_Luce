# Lemma 6.8: ideal traces

`Luce.Section6.lemma68 : Lemma68Contract.lemma68` proves both assertions of
`lem:sp-ideal-traces` in `fixed_points_sampled_profile.tex`. The separate
`lemma68_contractCheck` checks the exact closed target. Both are available
through `Luce.Section6`.

The statements use the literal ideal kernels, ordered distinct vertex
tuples divided by the cycle length, and the original convolution
coefficient. The index `k : Nat` denotes length `k+1`, including length
one. The root is the maximum left depth or minimum right depth, as required
by the largest-label convention. The core and root cutoffs retain their
actual ceilings, floors, and half-open inequalities.

The only model inputs are the original `PowerProfile` and active-corner
hypothesis. The proof constructs its analytic bounds from the explicit
increment density; integrability, derivative bounds, exponential moments,
and lattice estimates are proved, not assumed in the closed theorem.

## Proof

The continuous relative-coordinate trace is the integral of `(T-R)_+ W`
divided by the length. Exponential integrability of the range gives the
stronger expansion

`trace(A,B) = coefficient * log(B/A) - rangeMass + error`,

where the error is bounded by `E*(1+log(B/A))/A + D*exp(-c*log(B/A))`.
The logarithmic-cell comparison is proved quantitatively by telescoping
the product and bounding its derivative with an exponential envelope.
The bounded-row and target-entry estimates bound repeated-vertex terms
by a constant divided by `A`.

For the spatial assertion, exact finite-sum identities express the
root-restricted trace as a difference of two nested total traces. Their
common `rangeMass` cancels. This avoids the manuscript's cyclic-shift
orthant argument and its measure-zero tie analysis. The cutoff estimates
then give the manuscript bound with the stronger choices **K = 1** and
**kappa = 1**.

## Main files

- `Luce/Section6Lemma68Contract.lean`: both closed statements.
- `Luce/Section6IdealTraceAsymptotic.lean`: refined generic trace expansion.
- `Luce/Section6IdealTraceTotal.lean`: the total assertion.
- `Luce/Section6IdealTraceRestriction.lean`: exact nested-interval identities.
- `Luce/Section6IdealSpatialWindow.lean`: rounded core and threshold estimates.
- `Luce/Section6IdealSpatialEstimate.lean`: cancellation and spatial error.
- `Luce/Section6Lemma68.lean`: spatial assertion and full conjunction.
- `Luce/Section6Lemma68Audit.lean`: independent contract check.

## Verification

The full `lake build` passed, with 4374 jobs. The dedicated audit
`lake env lean audit/Section6Lemma68.lean` passed. It checks the elaborated
definitions, both closed theorem types, and transitive axioms, and raises
an error for any axiom outside `propext`, `Classical.choice`, and
`Quot.sound`. It also audits the refined expansion and principal analytic
and cutoff estimates. No `sorry` or extra axiom is used by these results.

Logs: `audit/section6-lemma68-full-build.log` and
`audit/section6-lemma68-audit.log`. The manuscript was not edited; its
SHA-256 remains
`b665b199bf513f537ad21a0f217a60c5bb889bea5812ffa17ab6e6437c36900e`,
matching the existing Lemma 6.9 snapshot.
