# Approved conditional fixed-point probability: complete

`Luce.predictable_fixed_point_probability` in `Luce/Section2PredictableProbability.lean`
proves the exact user-approved statement of `eq:predictable-p`. It is imported
by `Luce/Sections1To7.lean` and included in the default library build. This certifies that
statement; Section 2 as a whole remains incomplete.

## Manuscript and statement lock

Source: `fixed_points.tex:575`, label `eq:predictable-p`:

```latex
 p_{n,k}:=\Pp(I_{n,k}=1\mid\cF_{n,k-1})
 =\frac{\theta_{n,k}\one\{R_{n,k}\ge k\}}{W_{n,k}}.
```

The model input is the defining full permutation law `eq:luce-law`,
`fixed_points.tex:142`. For every full permutation sigma,

\[
P(\pi=\sigma)=\prod_{r=1}^n
\frac{\theta_{\sigma(r)}}{\sum_{j=r}^n\theta_{\sigma(j)}}.
\]

Under that law, for every label/draw position k,

\[
E_P[\mathbf1\{\pi^{-1}(k)=k\}\mid\mathcal F_{k-1}]
=\frac{\theta_k\mathbf1\{\pi^{-1}(k)\ge k\}}
{\sum_{i=1}^n\theta_i\mathbf1\{\pi^{-1}(i)\ge k\}}
\quad P\text{-a.s.}
\]

The unchanged approved proposition is recorded in
`proposals/Section2ConditionalProbability.lean`; the complete variable and
line-by-line correspondence is in `docs/section2-conditional-proposal.md`.
`audit/Section2PredictableProbability.lean` repeats that proposition and proves it
directly with the production theorem, thereby checking the full signature.

All quantified parameters and hypotheses are: an arbitrary sample type
`Ω : Type u`, its measurable-space instance `mΩ`, a measure `P` with
`IsProbabilityMeasure P`, `n : ℕ`, deterministic `w : Weights n`, the
permutation-valued map `π`, its measurability into the finite discrete sigma
algebra, equality of every full permutation probability to `w.mass`, and
`k : Fin n`. `Weights n` already requires each rate to be strictly positive.
The law is quantified over every permutation; the conditional identity holds
for every index, almost surely in the outcome. There are no new constants.

Lean's label `k` represents the paper's `k.val + 1`. Thus
`drawHistory π k.val` contains exactly the preceding draws. Existing history,
weights, rank, mass, and remaining-set definitions are unchanged. Conditional
probability is the conditional expectation of the indicator, with almost-sure
equality, as approved. No normalization of the rates, independent clocks,
positive-history-probability premise, integrability premise, or extra
finiteness/typeclass condition is added to the theorem.

## Proved dependency chain

1. `Weights.mass_decomposeFin` factors each full mass into its first-draw
   factor and the remaining mass after a bijective relabeling. The helper
   `Weights.removeFirst` keeps exactly the original remaining rates; positivity
   follows from the original weights.
2. `Weights.sum_mass` proves, by induction, that all full permutation masses
   sum to one. It uses no probability-space or normalization hypothesis.
3. `prefixAgrees` means equality at precisely the first m draw positions.
   `prefixMass` is the product of precisely those m factors in the original
   law. `sum_mass_prefix` sums over all full completions and proves that
   their total mass equals this partial product.
4. `sum_mass_prefix_next` proves that specifying the next label multiplies
   this prefix mass by its rate divided by remaining total weight, or zero
   if it is unavailable. An available next label is realized by an actual
   full permutation with the same prefix.
5. `drawHistory_eq_comap_prefixVector` identifies the exact approved history
   with its finite prefix-vector fibers. `predictableChance` is constant on
   those fibers. `fixed_point_mass_fiber_identity` proves the finite integral
   identity needed on each history fiber.
6. `condExp_finite_history_of_representatives` proves a generic finite-state
   conditional-expectation criterion, including equality of integrals on
   every history-measurable set. Its fiber hypothesis is explicitly discharged
   by the preceding mass identity and the given full distribution.
7. The final theorem rewrites the history and the existing ratio formula to
   obtain exactly the approved signature.

The generic helper's finite and decidable history/state conditions are
supplied by finite permutations, finite prefix vectors, and classical
reasoning. Unrepresented histories have zero sums and need no surjectivity
or positivity assumption. Integrability follows because every real function
of a finite state has finitely many finite real values under a probability
measure. History inclusion follows from the given measurability of π;
finiteness of the trimmed probability measure supplies sigma-finiteness.
The remaining set is nonempty, so positive rates imply a positive denominator.

No canonical Luce probability-space construction or equivalence with the
full independent-exponential race law is claimed by this theorem. Full-mass
normalization is proved independently; the approved target concerns any
supplied random permutation having the defining manuscript law.

## Important pinned mathlib dependencies

- `Equiv.Perm.decomposeFin`, `Mathlib.GroupTheory.Perm.Fin`:
  `Equiv.Perm (Fin (n + 1)) ≃ Fin (n + 1) × Equiv.Perm (Fin n)`.
  The accompanying inverse-application lemmas specify the first label and
  bijectively relabeled tail. This is a combinatorial equivalence, with no
  probabilistic content assumed.
- `MeasureTheory.integral_finsetSum`,
  `Mathlib.MeasureTheory.Integral.Bochner.Basic`: integrability of each summand
  permits interchanging a finite sum and an integral.
- `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`,
  `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`: for
  `hm : m ≤ mΩ` and a sigma-finite trimmed measure, an integrable f and an
  m-a.e.-strongly-measurable candidate g, integrable on every finite-measure
  m-measurable set, satisfy `g =ᵐ[P] P[f | m]` if their integrals agree on all
  such sets. All those obligations are derived in the finite-history helper.

## Verification

Run from the project root with pinned Lean/mathlib v4.33.1:

```powershell
lake build
lake env lean Luce/Section2PredictableProbability.lean
lake env lean audit/Section2PredictableProbability.lean
```

- Default `lake build`: PASS, 3642 jobs. Log:
  `audit/predictable-probability-build.txt`.
- Direct final-module check: PASS, exit 0, no diagnostics. Log:
  `audit/predictable-probability-module.txt`.
- Signature-lock proof, `#print`, and `#print axioms`: PASS, exit 0.
  All 36 reports contain only subsets of
  `[propext, Classical.choice, Quot.sound]`. The final theorem and exact
  statement-lock theorem have exactly those three standard axioms. Log:
  `audit/predictable-probability-print.txt`.
- All 13 transitive local source modules were scanned for prohibited proof
  placeholders and trust-bypassing constructs, with no matches. Module list:
  `audit/predictable-probability-dependency-files.txt`; empty scan result:
  `audit/predictable-probability-source-scan.txt`.
- Independent review of the statement and important dependencies found no
  mathematical change, added model assumption, circular conditional-choice
  hypothesis, or hidden unfinished proof.

The build replays preexisting linter/deprecation warnings. The statement-lock
audit retains the approved unused instance binder name `hP`, producing one
unused-name warning. There are no compilation errors or trust warnings.

## STATEMENT AUDIT

- Target theorem: `Luce.predictable_fixed_point_probability`.
- LaTeX source/label: `fixed_points.tex:575`, `eq:predictable-p`, under
  `fixed_points.tex:142`, `eq:luce-law`.
- Statement changed: NO.
- Hypotheses added: NO.
- Hypotheses strengthened: NO.
- Conclusion weakened: NO.
- Quantifiers changed: NO.
- Constant dependencies changed: NO.
- Definitions mathematically changed: NO.

## TRUST AUDIT

- New axioms introduced: NO.
- `sorry`/`admit` remaining in dependencies: NO.
- External assumptions used: NO. The explicit defining full distribution is
  an approved model hypothesis, not an unproved auxiliary theorem.
- `#print axioms` result:
  `[propext, Classical.choice, Quot.sound]`.
- Nonstandard axioms or suspicious dependencies: none found.

## BUILD AUDIT

- Relevant module checked: `Luce/Section2PredictableProbability.lean`, imported by
  the default `Luce` target.
- `lake build` result: PASS, 3642 jobs.
- Remaining errors: none in the completed target and checked dependency chain.
- Remaining Section 2 mathematics: the random-measure compensator assertion,
  the full uncapped Poisson criterion, and the remaining displayed proof
  assertions tracked in `docs/section2-status.md`.
