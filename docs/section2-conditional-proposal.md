# Approved Section 2 statement: the actual conditional fixed-point probability

This statement was approved and is now proved, without mathematical changes,
by `Luce.predictable_fixed_point_probability`. This document preserves the
statement review; see [the completed proof and audit](predictable-probability.md)
for current verification.

## Exact source and mathematical statement

`fixed_points.tex:575`, label `eq:predictable-p`:

```latex
 p_{n,k}:=\Pp(I_{n,k}=1\mid\cF_{n,k-1})
 =\frac{\theta_{n,k}\one\{R_{n,k}\ge k\}}{W_{n,k}}.
```

The row is a Luce permutation, whose defining full product law is given in
`fixed_points.tex:142`, `eq:luce-law`:

\[
P(\pi=\sigma)=\prod_{r=1}^n
\frac{\theta_{\sigma(r)}}{\sum_{j=r}^n\theta_{\sigma(j)}}.
\]

For a measurable random permutation with exactly this law, the approved theorem proves,
for each label `k`,

\[
E_P[\mathbf1\{\pi^{-1}(k)=k\}\mid\mathcal F_{k-1}]
=\frac{\theta_k\mathbf1\{\pi^{-1}(k)\ge k\}}
{\sum_{i=1}^n\theta_i\mathbf1\{\pi^{-1}(i)\ge k\}}
\quad P\text{-a.s.}
\]

This uses the now-approved `drawHistory` definition and existing positive
weights, Luce product masses, and remaining-weight definitions. No additional
mathematical definition is proposed. In particular the conditional choice
rule is the conclusion, not a hidden input.

## Locked Lean statement

The type-checked proposal is `proposals/Section2ConditionalProbability.lean`:

```lean
∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] {n : ℕ}
  (P : Measure Ω) [hP : IsProbabilityMeasure P] (w : Weights n)
  (π : Ω → Equiv.Perm (Fin n)),
  @Measurable Ω (Equiv.Perm (Fin n)) mΩ ⊤ π →
  (∀ σ : Equiv.Perm (Fin n), P.real {ω | π ω = σ} = w.mass σ) →
  ∀ k : Fin n,
    P[(fun ω => if (π ω).symm k = k then (1 : ℝ) else 0)
        | drawHistory π k.val] =ᵐ[P]
      (fun ω =>
        (if k ≤ (π ω).symm k then w.rate k else 0) /
          w.total (remaining (π ω) k))
```

## Complete correspondence and hypotheses

| Component | Mathematical meaning |
| --- | --- |
| `Ω : Type u`, `[mΩ : MeasurableSpace Ω]` | An arbitrary sample space and its sigma algebra; `u` is an implementation universe parameter. |
| `P : Measure Ω`, `[IsProbabilityMeasure P]` | The probability measure on that space. |
| `n : ℕ`, `w : Weights n` | Row size and all deterministic positive rates; positivity is already part of the approved model. |
| `π : Ω → Equiv.Perm (Fin n)` | The random permutation in draw order. |
| Explicit `Measurable ... mΩ ⊤ π` | The usual meaning of a random variable with values in the finite discrete permutation space. The codomain sigma algebra is not left unspecified. |
| `∀ σ, P.real {ω | π ω = σ} = w.mass σ` | Exactly the full Luce product law, for every deterministic permutation. Singleton probabilities determine this finite law. |
| `k : Fin n` | The paper's label and draw position `k.val + 1`; no extra `n > 0` assumption is needed. |
| `(π ω).symm k = k` | The paper's rank-based fixed-point event `R_k = k`. |
| `drawHistory π k.val` | Exactly the preceding draws, `F_(k-1)`. |
| `if k ≤ ... then w.rate k else 0` | The numerator `θ_k` times the availability indicator. |
| `w.total (remaining (π ω) k)` | Exactly `W_k`; this definition is unchanged. |
| `=ᵐ[P]` | Almost-sure equality, the correct equality notion for conditional expectation. |
| Bound variables `ω`, `σ`, and indices inside `w.mass`/`remaining` | Outcomes, all full permutations, and the finite indices in the displayed manuscript formulas. |

There is no normalization of the rates, no independence hypothesis, no
exponential representation, no fixed canonical probability space, no
positive-probability-history assumption, and no new constant. Neither
integrability nor sigma-finiteness of the trimmed probability measure is an
input; required facts must be derived from the stated probability model.

Interpretations approved by the user: represent the Luce distribution by all
its full permutation masses; make the discrete measurability of the random
permutation explicit; and read conditional probability as conditional
expectation of the indicator, equal almost surely. Index shifts and the
weighted `if` expression are mathematically equivalent implementations.

## Dependencies and proof obligations

Already available: `history_predictability`, `predictableChance_formula`,
`remaining_nonempty`, `Weights.total_pos`, and the choice bounds in
`Luce.Model`. The denominator is positive at every outcome, as a consequence
of a nonempty remaining set and positive rates.

The substantive step was to derive finite prefix-event probabilities from
the full product masses. It is now proved by `Luce.sum_mass_prefix`, using
`Luce.Weights.sum_mass`; `Luce.sum_mass_prefix_next` then derives the next-draw
rule. These are proved dependencies, not additional probability hypotheses.

Pinned mathlib results inspected:

- `MeasureTheory.sum_measureReal_preimage_singleton`,
  `Mathlib.MeasureTheory.Measure.Real:297`: the sum of the finite measurable
  fiber probabilities is the probability of their union/preimage. For a
  probability measure the required finite-fiber measure condition follows.
- `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`,
  `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic:253`: an
  appropriately measurable, integrable candidate agreeing in integrals on
  every history-measurable set equals the conditional expectation a.e.
  Its history inclusion and sigma-finiteness requirements must be discharged.

`Luce.Weights.sum_mass` now proves normalization of the product masses for
every positive weight vector, independently of a supplied probability model.
This stage does not package those masses as a canonical probability space or
derive the full exponential-race permutation law. Neither result is silently
assumed. The approved theorem takes an actual probability measure and random
permutation with the manuscript's defining law.

## Historical proposal verification

`lake env lean proposals/Section2ConditionalProbability.lean`: PASS, exit 0.
One harmless unused instance-name warning. Printed type and axioms checked:
`[propext, Classical.choice, Quot.sound]` for the proposition definition.
Log: `audit/section2-conditional-statement.txt`.

The proposal check established only that the statement was well-typed. The
subsequent approved proof, signature lock, direct module check, root build,
and all 36 axiom reports have now passed; see `predictable-probability.md`.
No axiom, external theorem assumption, `sorry`, or `admit` was added.
