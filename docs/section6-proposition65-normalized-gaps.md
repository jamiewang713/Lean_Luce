# Proposition 6.5: normalized-gap proof

The implementation proves the independent closed targets
`proposition65_localLaw : Proposition65Contract.localLaw` and
`proposition65 : Proposition65Contract.proposition65`.
`Section6Proposition65Audit.lean` checks the full proposition separately.
The statement, profile assumptions, sampling grids, kernels, and toolchain
are unchanged. The global conclusion is supplied by `lemma64_matrix`.

## Proof

The separated insertion identity is used on the actual deleted exponential
race. Rank separation supplies distinct finite gap indices; the endpoint
buffer and the exact left/right displacement bounds discharge the gap-law
premises. The marked normalized gaps therefore have their proved joint
unit-exponential law. The insertion factors themselves remain dependent.

`Section6ProfileJointWindow` derives joint time/weight probability bounds
from the profile quantile tails, lower bounds for the deleted count means,
and the existing random-time weight estimate. `Section6QuarterWindow`
chooses the lower cutoff so that width h^(-1/4) satisfies all window and
deletion conditions. The resulting per-edge failure probability is bounded
by J h^(-1/2). This proof needs no exponential weight-concentration theorem.

`Section6CrossDepthProfile` derives off-diagonal rate-time and hazard
asymptotics from the sampled rates and the existing same-depth estimates.
`Section6NormalizedLocalPointwise` combines these estimates with the actual
time/weight event. Taylor expansion at time zero, followed by multiplication
by the survival factor, gives an error bounded by

    C H (epsilon xi + xi^2/h).

Extra factors of the corner ratio are absorbed into exponential slack.
No truncation of the normalized spacing is needed. The final envelope decay
is a common positive value smaller than both the pointwise and moment
decays at every active corner.

`Section6NormalizedGapMoments` proves the weighted mixed-moment identities
needed by telescoping: the gap product has mean one and each product with
one additional coordinate has mean two. `Section6EventIntegral` and
`Section6InsertionSecondMoment` supply Cauchy--Schwarz and finite Holder on
the original probability space. `Section6JointNormalizedEstimate` combines
the individual events by a union bound. It never assumes independence
between the event and the normalized gaps.

`Section6Proposition65Sum` chooses common constants over the finite type of
active corners. It uses v=1/16, moment ceiling 2 max(1,r), delta<=1/4,
and kappa=min(1/8,rho0/2), with rho0 a positive lower bound for the derived
corner error exponents. It then restores the original marking order.
`Section6Proposition65` enlarges the final constant by max(1,r) to prove
both the summed error and the interval consequence with the same constant.

The zero-mark case is proved directly from the empty cylinder. In this
case the contract places no restriction on B. The auxiliary
`small_rpow_nonneg` handles a potentially negative B/n for the chosen small
positive kappa, without adding B>=0 to the contract.

## Scope and verification

The closed theorem quantifies over both supported grids, every permitted
profile, either or both active corners, all marked configurations in the
stated domain, and the cutoff boundaries. Its global matrix component
covers adjacent ranks and the other configurations. All integrability and
probabilistic inputs to the helper lemmas are discharged in the closed
proof. Conditional helper lemmas are not substituted for the proposition.

The dedicated audit is `audit/Section6Proposition65.lean`; it prints the
contract and all 63 new theorem types and transitive axiom dependencies.
Build, audit, and frozen-file results are recorded alongside it in `audit`.

The final full build passed (4331 jobs). The dedicated audit passed for
exactly 63 theorem declarations across 23 new modules, with no missing
reports or Lean errors. All transitive dependencies use only `propext`,
`Classical.choice`, and `Quot.sound`. The new sources contain no proof
placeholders, added axiom declarations, unsafe implementations, or
elaboration-time proof escapes. The elaborated contract definitions and
theorem types are preserved in `audit/section6-proposition65-audit.log`;
the machine-readable results are in
`audit/section6-proposition65-validation.json`.

The unmodified whole-Section-6 audit generator was rerun. Its snapshot
contains 847 source theorem declarations, with 825 successful reports
using only permitted axioms. The remaining 22 declarations belong to
unrelated concurrent increment-density, convolution-density, and
continuous-trace work that is absent from the aggregate imports. An
attempt to include an already compiling increment-envelope module met
a proof error after that file changed concurrently; the extra import
was removed and those sources were left untouched. The all-source audit
and historical validator therefore remain failed, separately from the
passing Proposition 6.5 audit and full project build. The exact audit
input and output are preserved as
`audit/Section6CurrentProposition65Snapshot.lean` and
`audit/section6-proposition65-current-audit.log`.

The initial check in this implementation run already found that
`fixed_points_sampled_profile.tex` differs from the 47-file Proposition 6.5
snapshot. The other 46 entries match. The manuscript was not edited in
this run, and no historical snapshot or checker was changed. The historical
freeze discrepancy is reported separately from proof verification.

This completion concerns Proposition 6.5. Later Section 6 CLTs remain
outside its scope. Earlier unresolved-status entries in the cumulative
ledger describe historical checkpoints, superseded for this proposition
by this proof.
