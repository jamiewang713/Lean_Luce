# Migration to the endpoint shell-capacity assumption

Source authority for this generalization: `fixed_points_shell_condition.tex`, in particular `ass:fixed-endpoint` (lines 272–280). This is a dependency and proof-design review, not a claim that the generalized Lean proofs have been completed. Existing production Lean files have not been changed by this review.

## Exact mathematical change

For terminal depth `1 ≤ m ≤ n`, put `k(n,m) = n-m+1`. For integers `j ≥ 1`, define

\[
 D_{n,j}=\{m\in\{1,\dots,n\}:j\le\log(n/m)<j+1\}.
\]

For nonempty shells put `r(n,j) = max D(n,j)` and `b(n,j) = min {θ(n,k(n,m)) : m ∈ D(n,j)}`. The replacement assumption is

\[
 \lim_{J\to\infty}\limsup_{n\to\infty}
 \sum_{j\ge J,\ D_{n,j}\ne\varnothing}\exp(-b_{n,j}j)=0.
\]

Normalization remains the separate `NormalizedWeights` hypothesis, and `Weights` continues to enforce strictly positive finite-row rates. There is no fixed positive lower bound on all sufficiently terminal rates. `ProfileLimit` remains unchanged.

Recommended names during migration: preserve the old predicate as `UniformEndpointAssumption`, and introduce `EndpointShellAssumption` for the new predicate. Once downstream proofs are ported, the public `EndpointAssumption` name can denote the shell version. Prove that the uniform condition implies the shell condition, so the old finite-mean conclusions follow as corollaries. Do not redefine the old name first and leave existing proofs destructuring it as a tuple of constants.

## Definition details that matter

- A shell can be represented as a finite set of labels `k : Fin n`, with depth `n-k.val`. This is the exact one-based manuscript convention, including depth one at the last label.
- Define floors and maxima for nonempty shells. Empty shells have zero cost and must not contribute an artificial minimum or an exponential term equal to one.
- The row has only finitely many nonempty shells. Use a proved finite index bound, or the finite image of the shell-index map, to implement the sum.
- Avoid defining the assumption using only a totalized real `limsup` without bounding its row sequences. An extended-nonnegative formulation is safe. An equivalent practical quantified formulation is: for every `η > 0`, there is an integer `J ≥ 1` such that eventually in `n` the shell tail sum is less than `η`. Nonnegativity and monotonicity in `J` give the iterated extended-limit formulation. Preserve the order `η, J, n`; a separate row threshold for each individual shell is insufficient.
- Prove the shell partition and spatial-cutoff comparison, including the rounding difference between depth `m ≤ n exp(-J)` and label `k > (1-exp(-J))n`.

## The substantive Section 4 replacement

The existing route is uniform endpoint rates → a power bound in ε → vanishing tail probability and finite intensity. The new route is shell capacity → buffered shell sums → vanishing tail expectation → the same qualitative conclusions.

The new manuscript supplies three main ingredients:

1. **Block endpoint capacity**, lines 919–988: for a nonempty depth block, with minimum rate `a`, maximum depth `r`, cutoff `t > 0`, and `B = S(t)-1 > r`, prove
   \[
   E[\text{fixed points in the block}]
   \le |\mathcal B|\exp(-(B-r)^2/(2B)) + Q(at),
   \qquad Q(x)=-\log(1-e^{-x}).
   \]
   This reuses the rank-integral identity and exponential-clock independence. New analytic ingredients are monotonicity of `a/(exp(a*t)-1)` and its tail integral. The existing half-mean Chernoff estimate suffices for a weaker block bound adequate for shell tightness; proving the displayed block proposition exactly requires the general deviation parameter as well.
2. **Diagonal shell buffer**, lines 1087–1118: with `h(j)=sqrt(j)`, prove that the iterated tail sum of `Q(b(n,j)*(j-h(j)))` vanishes. The bound comes from splitting `b(n,j)*j` at `sqrt(j)`, with the summable error `exp(1-sqrt(j))`. In particular, all nonempty sufficiently late shells eventually have `b(n,j)*(j-h(j)) > 1`, uniformly within a row tail.
3. **Shell endpoint expectation tightness**, lines 1120–1179: apply the block estimate at `t=log(n/r(n,j))-sqrt(j)` and sum over shells. Crucially, add the sharp Jensen bound `S(t) ≥ n*exp(-t)` under normalization. The existing bound in `Section4EndpointEstimates.lean:68`, `S(t) ≥ (n/2)*exp(-2*t)`, loses a factor in logarithmic time and cannot supply this argument under the stated shell assumption. Distinct shell maxima control the early terms by `sum_{r≥1} r*exp(-c*r*exp(sqrt(J)))`.

The reusable output should be expectation tightness, for example: for every `η > 0`, some `α < 1` has eventually in `n` expected fixed-point count in `(α,1]` below `η`. Tail monotonicity supplies the limit as `α ↑ 1` and eventual boundedness. Probability tightness alone is not the right interface for the current intensity argument.

The explicit bound `2^(1+γ/2)*ε^(γ/4)` belongs to the stronger uniform-rate case. The shell assumption supplies vanishing tails without that prescribed power modulus.

## Existing files to modify or reconnect

These 13 production files directly mention `EndpointAssumption`:

| File | Required action |
|---|---|
| `Luce/Section1Assumptions.lean` | Introduce shell definitions/predicate (possibly in a separate imported module); retain the uniform predicate under an explicit name. |
| `Luce/Section4TailAssumptions.lean` | Retain uniform-to-power estimates as stronger-case results; add or import the shell-to-expectation-tightness bridge. |
| `Luce/Section4TailTightness.lean` | Derive `tail_fixed_point_tightness` from shell expectation tightness and Markov, replacing its use of the power-bound helper. |
| `Luce/Section4Endpoint.lean` | Retain the finite uniform estimate; replace the general assumption-level tail expectation interface with a qualitative one. Reuse arbitrary-space law transfer. |
| `Luce/Section4Count.lean` | Pass the shell hypothesis to the new tail theorem. Exact point-measure/count identities remain applicable. |
| `Luce/Section4IntensityEstimate.lean` | Replace `section4_intensity_test_bound`'s power modulus with arbitrary small tail-test bounds. Its observed-test comparison and expectation lower bound are reusable. |
| `Luce/Section4Intensity.lean` | Rework `section4_interior_intensity_bounded` to use one finite qualitative tail bound. Reconnect full-intensity finiteness, diagonal integrability and intensity-tail convergence. |
| `Luce/Section4FullIntensity.lean` | Change hypothesis plumbing for `fullIntensity` and its identities; preserve the same diagonal density. |
| `Luce/Section4Poisson.lean` | Reconnect terminal approximation to the generalized tightness and finite intensity. |
| `Luce/Section4TotalVariation.lean` | Change hypothesis plumbing; reuse the law and total-variation arguments. |
| `Luce/Section4Theorem.lean` | State canonical and arbitrary-space main Poisson theorems under the shell assumption. Their conclusions stay the same. |
| `Luce/Section5ExceptionalLow.lean` | Replace the global low-label-to-interior argument with compact low-rate truncation. Preserve the original global result under the uniform assumption. |
| `Luce/Section5Reservoir.lean` | Update only the unit-weight example's endpoint hypothesis, preferably via uniform ⇒ shell. The reservoir proofs themselves are unaffected. |

Proposed new modules, with names subject to implementation choices:

- `Section4EndpointShells.lean`: finite shells, costs, assumptions, old-condition implication.
- `EndpointCapacity.lean`: `Q`, the block bound, sharp Jensen survivor bound.
- `Section4EndpointShellBuffer.lean`: buffered tail estimates and summability.
- `Section4EndpointShellTightness.lean`: expectation tightness and cutoff rounding.
- `Section5CompactLow.lean`: low-rate truncation on a fixed compact label interval.
- `Section5MarkedReturn.lean`: maximum-rooted cycle count and marked return/edge bounds.
- `Section5ShellTightness.lean`: short-cycle endpoint tightness.

Some helpers may naturally extend existing `EndpointProbability`, `EndpointIntegrals`, `Section5LowCycleRows`, or ghost-window modules. `Luce/Sections1To7.lean` and the Section 4/5 aggregate imports must include the new proof chain.

## Section 5: the second genuine change

At `Section5ExceptionalLow.lean:36`, the proof destructures the old endpoint condition to obtain `γ, ε₀, n₀`. At lines 45–53 it proves that every label with rate below `δ < γ` lies in a fixed compact interior interval. This inference is unavailable under shell capacity.

The revised manuscript changes the order of arguments:

1. Keep global high-rate truncation from `Section5ExceptionalHigh.lean`.
2. Prove low-rate truncation only for labels `k ≤ β*n`, for each fixed `β < 1`, without an endpoint hypothesis (source lines 1511–1586). Reuse `ProfileLimit.bounded_cycle_probability_uniform`, the interior ghost-window estimate, low-rate density convergence, and the existing orbit charging inequality. The constant can depend on `β`, the cycle-length cutoff and the high-rate cutoff.
3. Add short-cycle shell tightness (source lines 1591–1730). Rotate a cycle at its unique maximal label, preserve its predecessor `u < v`, and derive the marked return/edge bound from ghost row sums and bounded window overlap. Bound early target-shell windows by a survivor Chernoff estimate. Bound late terminal-source contributions by buffered shell costs; bound late compact-source contributions by `exp(-δ*(J-sqrt(J)))`. Preserve cutoff order: `M`, then `J₀` and `β`, then `δ`, then `J`, before row limits.
4. Use Lemma 5.2 and the existing finite cycle-counting identities to finish the compact factorial-moment limit. Use short-cycle shell tightness to prove finite full cycle intensities and remove the cutoff, then prove the joint weak and total-variation conclusions (source lines 1732–1768).

The new cycle-shell tightness is additional proof work, not a theorem already supplied by the existing project. The old pending Lemma 5.5 roadmap should be superseded by this manuscript's argument. The generic factorial-moment-to-Poisson and vector total-variation completion was already unfinished and remains necessary.

After cycle-shell tightness, a global low-rate conclusion can also be recovered by splitting at `β`: compact low-rate vertices are controlled by step 2, and at most `L` vertices occur per discarded short cycle meeting the terminal interval. Using that global conclusion to prove step 3 would be circular.

## What can be reused

The finite model, exponential-race law, rank integral, two-candidate identity, history/conditional-probability results, predictable Poisson criterion, Section 3 interior proofs, profile analysis, Lemma 5.2 and its gap analysis, finite cycle combinatorics, finite insertion/resampling/ghost-cylinder machinery, and high-rate truncation do not need stronger mathematical assumptions. Existing uniform endpoint estimates remain useful stronger-case lemmas; they need not be deleted.

No extra mathematical axiom is needed. The new estimates must be proved as theorems, not added as hypothesis fields of the shell assumption.

## Source contracts and verification

Update `docs/assumptions.md`, the Section 4 status/tail-tightness records, and `SECTION5_FORMALIZATION.md` to refer to the shell manuscript for generalized results. Historical audits should continue to identify which statement version they checked. `main.tex` currently inputs `fixed_points.tex`; record the shell file explicitly as the new proof authority rather than silently relying on that entry point. Use manuscript labels as well as numbers, since added propositions change numbering.

Add statement and axiom audits for the shell definition, uniform ⇒ shell, buffered capacity, expectation tightness, compact low-rate truncation, short-cycle tightness and the final generalized theorems. Expand their actual types and custom predicates, run the full build, and check for no admissions or custom axioms. The exceptional-label refinement at source lines 1182–1228 is a separate optional fixed-point generalization; it is not part of this shell-assumption replacement and is not asserted there for short cycles.

## Suggested implementation order

First implement the shell predicate and uniform-condition implication. Then prove the buffered block estimates and expectation tightness. Reconnect Section 4 and audit the generalized fixed-point theorem. Next prove compact low-rate truncation and short-cycle shell tightness. Finally complete the joint short-cycle Poisson theorem using the existing interior local limit and counting machinery.
