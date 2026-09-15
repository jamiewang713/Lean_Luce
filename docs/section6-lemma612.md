# Lemma 6.12: interior-grid sampling

The manuscript's `lem:sp-interior-grid` is formalized by
`Luce.Section6.lemma612` in `Luce/Section6Lemma612.lean`.
Its independent statement, `Lemma612Contract.lemma612`, imports only the
existing Section 6 contract definitions and asserts the conjunction

```lean
SampledProfileContract.powerLaw.{u} .interior ∧
  SampledProfileContract.spatial.{u} .interior ∧
  SampledProfileContract.critical.{u} .interior
```

The interior sampling definition is `((i.val : ℝ) + 1) / ((n : ℝ) + 1)`
for `i : Fin n`, exactly the manuscript's one-based sampling at `i/(n+1)`.
All profile assumptions, arbitrary probability spaces, full Luce masses,
mean asymptotics, Gaussian limits, and spatial localization assertions are
inherited from the unchanged original contracts. The critical conclusion
also includes the uniform mean bound for every fixed longer cycle.

## Proof and dependencies

The proof specializes these already proved theorems to `.interior`:

| Manuscript conclusion | Direct Lean dependency |
| --- | --- |
| Theorem 1.6: power-law cycle means and joint CLT | `Luce.Section6.powerLaw65` |
| Theorem 1.7: spatial means, joint CLT, and localization | `Luce.Section6.spatial65` |
| Theorem 1.8: critical-pole fixed points and longer-cycle means | `Luce.Section6.critical` |

Their analytic and probabilistic proofs already quantify over both sampling
grids. In particular, the population and sampled endpoint estimates include
the interior grid before the limit theorems are proved. The final conjunction
therefore needs no additional asymptotic estimate or model assumption.
See `section65-power-law-clts.md` and `section6-critical.md` for the underlying
proofs and their earlier lemma dependencies.

`Luce.Section6.section6` also assembles the midpoint specializations with
Lemma 6.12 to prove the entire existing `SampledProfileContract.section6`.
This is the precise scope of that closed target; it does not assert that
every ancillary result elsewhere in the manuscript has been formalized.

`Section6Lemma612Audit.lean` checks the lemma directly against the three
original interior-grid propositions, and separately checks the full Section 6
target. Both checks are imported through `Luce.Section6` and the default
`Luce` library. This task did not edit the TeX manuscript or the pre-existing
contract definitions.

## Verification

The reproducible checks are:

```powershell
lake build
lake env lean audit/Section6Lemma612.lean
```

The dedicated audit imports `Luce`, prints the exact sampling and contract
definitions, and checks the types and transitive axioms of all four new
theorems. `audit/section6-lemma612-contract-freeze.json` records the ten
original manuscript, contract, direct proof dependency, and toolchain hashes
captured before this work. Historical audit baselines are preserved.

Results are recorded in `audit/section6-lemma612-validation.json`:

- Full default build: **passed, 4567 jobs**.
- All **four theorem types and transitive axiom reports passed**. Only
  `propext`, `Classical.choice`, and `Quot.sound` occur.
- The three new proof/contract modules contain no proof placeholders,
  additional axioms, or checking bypasses.
- All nine original Lean input and toolchain hashes match the initial
  snapshot. The manuscript was edited separately during the build, so its
  whole-file hash differs. Its current Lemma 6.12 statement was re-read and
  is unchanged. That mismatch is recorded separately from the passing proof
  checks; the saved baseline was not reset.
