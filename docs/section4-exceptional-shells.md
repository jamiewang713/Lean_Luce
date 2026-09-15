# Lemma 4.3 and Corollary 4.7

Source: `fixed_points_sampled_profile.tex`, labels `lem:slow-label-charge`
and `cor:exceptional-shell-refinement`.

## Public statements

| Manuscript statement | Lean declaration | File |
| --- | --- | --- |
| Lemma 4.3, arbitrary Luce realization | `Luce.individual_slow_label_charge` | `Luce/EndpointSlowLabel.lean` |
| Lemma 4.3, exponential-clock ranks | `Luce.race_individual_slow_label_charge` | `Luce/EndpointSlowLabel.lean` |
| Corollary 4.7, both endpoint expectation limits | `Luce.corollary47_endpoint` | `Luce/EndpointExceptionalTheorem.lean` |
| Corollary 4.7, literal `ε ↓ 0` parameter | `Luce.corollary47_epsilon` | `Luce/EndpointExceptionalTheorem.lean` |
| Corollary 4.7, full finite-mean Poisson conclusion | `Luce.corollary47` | `Luce/EndpointExceptionalTheorem.lean` |
| Same Poisson conclusion on arbitrary row probability spaces | `Luce.corollary47_general` | `Luce/EndpointExceptionalTheorem.lean` |
| Literal limiting intensity | `Luce.exceptionalFullIntensity_projection` | `Luce/EndpointExceptionalTheorem.lean` |

The default `Luce` entry point imports these results.

## Exact objects and assumptions

Labels use `Fin n`: manuscript label `k` has value `k-1`, and terminal depth
is `n - k.val`. An exceptional-depth set is represented by its corresponding
labels `E n : Finset (Fin n)`. There is no restriction on how this set varies
with `n`.

`deletedSmallestRateSum w k` is the minimum total rate over all subsets of
`univ.erase k` with `n-k.val-1` elements. This is the sum of the prescribed
number of smallest rates, including ties. Its nonempty indexing set,
attainment, nonnegativity, and comparison with every admissible subset are
proved. In depth one, the unique admissible subset is empty.

`RegularShell.terminalShell E n j` is exactly `terminalShell n j \ E n`.
Its floor is the finite minimum on this set. Empty regular shells have zero
cost. `EndpointExceptionalAssumption w E` is exactly the iterated limit of
the sum of regular exponential shell costs and the individual exceptional
charges at depths `m ≤ n exp(-J)`. Normalization is separate; neither a
buffered condition nor a tail bound is an assumption.

As in the existing shell formalization, raw nonnegative iterated limsups
are taken in `ℝ≥0∞`. The endpoint theorem also proves the real-valued
expectation limits. The conversion derives eventual row boundedness from
the extended limit, so divergent sequences are not silently assigned a
totalized real limsup. Both `α ↑ 1` and the literal `ε = 1-α ↓ 0`
parameterizations are included.

The endpoint conclusions require only normalization and the combined cost
condition. The full Poisson conclusion additionally uses the existing
`ProfileLimit w f`. It proves integrability of the diagonal density, weak
convergence of the entire finite point measure, and total-variation
convergence of its count with parameter `∫ x in Ioo 0 1, profileDiagonal f x`.
The general realization theorem assumes precisely measurability and the
defining finite Luce masses, with no coupling requirement across rows.

## Proof structure

1. The surviving set before the candidate's draw has the required
   cardinality. Deleting the candidate leaves an admissible subset, which
   bounds its conditional choice probability by the individual charge.
   Integrating the already-proved conditional probability identity gives
   Lemma 4.3.
2. The existing block-capacity and square-root-buffer arguments are proved
   for regular subsets in `EndpointRegularShells` and
   `EndpointRegularShellLimit`. Normalization applies to the original full
   row of clocks.
3. `EndpointShellPartition` proves the exact weighted shell partition,
   including the boundary `m = n exp(-J)`. `EndpointExceptional` splits
   the expected fixed-point count into regular and exceptional terms,
   bounds the latter by Lemma 4.3, and proves endpoint tightness.
4. `EndpointTailPoisson` expresses the existing intensity and Poisson
   completion using an internal endpoint expectation interface.
   `EndpointExceptionalTheorem` supplies that interface from the raw
   combined condition; it is not an extra hypothesis of the public result.

## Reproducible verification

```powershell
lake build
lake env lean audit/Section4Exceptional.lean
```

The audit checks a statement with the combined assumption and terminal
expectation expanded, prints the public types and defining objects, and
prints transitive axiom dependencies of both results.

Verified on 2026-09-14 with Lean 4.33.1 / mathlib v4.33.1:

- `lake build` passed (4591 jobs), including the default library entry point.
- `lake env lean audit/Section4Exceptional.lean` passed, including the
  depth-one boundary case and the expanded raw-condition statement.
- Every audited declaration depends only on `propext`, `Classical.choice`,
  and `Quot.sound`. There is no `sorryAx` or additional axiom.
- The eight added production modules contain no proof placeholders,
  custom axioms, unsafe declarations, or native-evaluation proof shortcuts.

Compiler records: [library build](../audit/section4-exceptional-full-build.log)
and [statement/axiom audit](../audit/section4-exceptional-audit.log).
