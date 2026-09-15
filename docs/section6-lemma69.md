# Lemma 6.9: overlaps and nearby ranks

The implementation proves `lemma69 : Lemma69Contract.lemma69`, with the
separate `lemma69_contractCheck` in `Section6Lemma69Audit.lean`. Both are
imported through `Luce.Section6`. The independent contract and its
definitions were frozen before completing the proof; the snapshot also
covers their dependencies, the manuscript, and the toolchain files.

The statement is the deterministic matrix lemma in
`fixed_points_sampled_profile.tex`, `lem:sp-collisions`. Its inputs are
exactly the nonnegative domination matrix, its uniform row bound and
core-target bound, and the pointwise domination of the proposed joint
weight. These are the matrix hypotheses stated in the manuscript, not
additional assumptions on the sampled profile. No cycle collision,
summability, independence, or probability bound is assumed.

`CollisionAssignment` is the literal finite family of ordered vertex
tuples. Each cycle has its own corner and positive length at most L.
Every vertex lies in its specified core [A,B]. Tuple entries need not be
distinct: this is essential for bounding overlaps in ideal products.
The joint weight is the product of matrix entries on the cyclic edges.
`collisionPairSum` restricts to two distinct slots whose actual label
values have natural-number distance at most D. `collisionUnionSum`
restricts to the union of these events over all distinct pairs. Additional
restrictions can be represented by a smaller dominated joint weight.

## Proof

`Section6CollisionPaths` propagates a target bound through an open path
using only bounded row sums. `Section6CollisionCycleTests` cuts the
closing edge, uses finite cyclic reindexing to move an arbitrary selected
slot to the first position, and proves one-slot and two-slot test-function
inequalities. The two slots in one cycle give two reciprocal-depth
factors. For slots in different cycles, finite summation of their two
one-slot estimates gives the same factors.

`Section6CollisionDepthSums` proves the harmonic trace bound and the
square-reciprocal bound 2/A for a core. Each label has at most 2D+1 nearby
labels. Applying 2uv <= u^2+v^2 therefore proves the bound

    sum over nearby labels of 1/(depth(a)*depth(b)) <= 2(2D+1)/A.

This works for either choice of the two corners, even when their cores
overlap. Thus the manuscript proof's eventual separation claim B=o(n)
is unnecessary; no such premise was added. For two slots in the same
corner, `collision_same_corner_distance` proves that label distance and
endpoint-depth distance agree exactly.

`Section6CollisionProductSums` factors the sums over the unaffected
cycles. Each is bounded by a harmonic trace. The same-cycle case leaves
s-1 traces; the different-cycle case leaves s-2, which is bounded by the
required s-1 power because the harmonic factor is at least one.
`Section6CollisionUnion` applies a finite union bound and bounds the
number of ordered slot pairs by (sL)^2.

The final proof explicitly chooses C' = max(1,C), Q = (C')^L,

    M = 2(2D+1) Q^2 Q^(s-1),
    K = ((sL)^2+1) M.

One positive K bounds both the specified-pair sum and the all-pairs
union by K/A * (1+log(B/A))^(s-1), uniformly in n, A and B.

## Scope and verification

The theorem covers empty families, one-vertex cycles, two slots of the
same cycle, slots of different cycles, repeated vertices, D=0, either
corner and mixed corners, A=B, and the exact cutoff boundaries. An empty
core also causes no difficulty. No condition B=o(n), core disjointness,
or lower bound on the number of cycles is imposed.

The dedicated type and axiom audit is `audit/Section6Lemma69.lean`.
Final build, audit, source-scan and snapshot results are recorded in
`audit/section6-lemma69-validation.json`. Historical snapshots and
checkers are preserved; any unrelated whole-Section-6 audit failures
are reported separately from this lemma's checks.

Final verification: the target build passed (3684 jobs), and the full
project build passed (4342 jobs). All 34 new theorem declarations across
11 modules passed the dedicated type and transitive axiom audit, using
only `propext`, `Classical.choice`, and `Quot.sound`. The source scan found
no proof placeholders, added axioms, unsafe implementations, or
elaboration-time proof escapes. All 14 files in the Lemma 6.9 snapshot
match, including the manuscript and toolchain files.

The unmodified all-source audit generator was also rerun. Its preserved
input is `audit/Section6CurrentLemma69Snapshot.lean` (950 declarations).
That audit produced 531 permitted-axiom reports before reaching the
unchanged 100-error limit on 50 unimported declarations from concurrent
Lemma 6.8 work. It therefore does not constitute a passing whole-source
audit; the dedicated Lemma 6.9 audit checks every new theorem independently.
The older 47-file and 13-file snapshots retain their pre-existing
manuscript mismatch. No old baseline, checker, or unrelated proof was
changed to suppress these failures.
