# Section 6.6: critical pole

The complete critical-pole theorem is proved in `Luce/Section6Critical.lean`:

```lean
theorem Luce.Section6.critical (grid : SamplingGrid) :
  SampledProfileContract.critical grid
```

`Section6CriticalAudit.lean` checks the independent closed contract and its
midpoint and interior specializations. The theorem is imported by `Luce.Section6`.
It proves the fixed-point Gaussian limit centered at `log (log n)` and scaled by
its square root, the mean asymptotic, and uniformly bounded expected counts for
each fixed cycle length at least two. It applies to arbitrary probability spaces
and measurable permutations with the full Luce masses. All intermediate estimates
are derived from the original critical profile and exact sampling assumptions.
The TeX manuscript was not edited.

## Proof structure

The fixed-point argument approximates the actual predictable probabilities by
`1 / (m * log (n/m))` on the block from `ceil (sqrt n)` to `floor (eps*n)`.
Population integral comparisons, deterministic remaining-rate bounds, and arrival
concentration give a summable error in expected absolute value. The early and late
blocks contribute a bounded expectation. The deterministic reference has mass
`log (log n) + O(1)` and bounded square sum. The proved adapted Bernoulli criterion
then gives the Gaussian limit; equality of expected count and compensator gives
the mean asymptotic. `Section6CriticalFixedPoints.lean` transfers both conclusions
from the exponential race to any permutation with the same Luce law.

For longer cycles the proof uses a fixed lower cutoff, which simplifies the
manuscript argument. A deterministic deleted-rate floor and an arrival-tail bound
give a direct exponential insertion kernel estimate. The arrival error is absorbed
into the kernel's exponential decay. A closed cycle has a sufficiently large drop
in logarithmic labels; summing the resulting decay over its other vertices bounds
the probability of a retained cycle with maximum label `m` by
`C / (m * log(n/m)^(3/2))`. Summing over maxima is uniformly bounded. Cycles outside
the retained block cost at most the fixed number of early labels plus the proved
late-vertex expectation bound. Small values of `n` are absorbed by increasing the
constant. This avoids a simultaneous-background event and a growing lower cutoff.

| Component | Main modules |
|---|---|
| Critical profile and population bounds | `Section6CriticalProfileBounds`, `Section6CriticalPopulationEstimates` |
| Predictable probability approximation | `Section6CriticalMainProbability`, `Section6CriticalReferenceBounds` |
| Fixed-point CLT and mean | `BernoulliReferenceApproximation`, `BernoulliReferenceMean`, `Section6CriticalFixedPoints` |
| Actual insertion kernel | `Section6CriticalDeletedFloor`, `Section6CriticalGapSurvival`, `Section6CriticalInsertionLp`, `Section6CriticalShiftLog` |
| Cycle decay and summation | `Section6CriticalCycleDrop`, `Section6CriticalCycleKernel`, `Section6CriticalRootProbability`, `Section6CriticalLongerCycles` |
| Closed theorem and contract checks | `Section6Critical`, `Section6CriticalAudit` |

## Verification

- Full default build: **passed, 4564 jobs** (`audit/section66-full-build.log`).
- Dedicated elaborated-type and transitive-axiom audit: **122 declarations,
  including 111 theorems in 46 modules**, all checked.
- Only `propext`, `Classical.choice`, and `Quot.sound` occur in the axiom reports.
  The source check found no proof placeholders or additional axioms.
- The three original Section 6 contract/profile-definition files match their
  preserved baseline hashes. No baseline was reset. This comparison does not
  assert equality of every file in the older snapshot.
- The audit generator, Lean audit, and validator are
  `audit/generate_section66_audit.py`, `audit/Section66Closed.lean`, and
  `audit/validate_section66.py`. Results are in `audit/section66-validation.json`.

Earlier progress entries describing the critical application as open are
historical and are superseded by this completion record.
