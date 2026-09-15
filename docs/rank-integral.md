# Approved pilot: Lemma `lem:rank-integral`

Statement and definitions approved by the user on 2026-09-10. This record concerns
only this lemma. It does not certify the other manuscript results or completion
of Sections 1–4.

## Manuscript source

`fixed_points.tex:835`, Section 4, “The last few positions,” lemma
`lem:rank-integral`, equation `eq:rank-integral`:

```latex
\begin{lemma}\label{lem:rank-integral}
For every label $k$,
\begin{equation}\label{eq:rank-integral}
 \Pp(R_k=k)=
 \int_0^\infty \theta_k e^{-\theta_k t}
 \Pp\left(\sum_{j\ne k}\one\{E_j>t\}=n-k\right)dt.
\end{equation}
\end{lemma}
```

The model uses positive rates and independent exponential clocks. The rank is
specified by `eq:rank-representation` at `fixed_points.tex:161`:

\[
R_{n,i}=1+\sum_{j\ne i}\mathbf 1\{E_{n,j}<E_{n,i}\}.
\]

## Locked definitions and statement

The definitions and theorem live in namespace `Luce` in
`Luce/ApprovedRankIntegral.lean`. The following is the approved interface;
the theorem body is omitted here because this is a statement record.

```lean
noncomputable def rankOf {n : ℕ}
    (e : Fin n → ℝ) (k : Fin n) : ℕ := by
  classical
  exact 1 +
    ((Finset.univ.erase k).filter
      (fun j => e j < e k)).card

noncomputable def otherSurvivors {n : ℕ}
    (e : Fin n → ℝ) (k : Fin n) (t : ℝ) : ℕ := by
  classical
  exact ((Finset.univ.erase k).filter
    (fun j => t < e j)).card

theorem rank_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (n : ℕ)
    (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i)
    (E : Fin n → Ω → ℝ)
    (hLaw : ∀ i,
      ProbabilityTheory.HasLaw
        (E i) (ProbabilityTheory.expMeasure (θ i)) P)
    (hIndependent : ProbabilityTheory.iIndepFun E P)
    (k : Fin n) :
    P.real {ω | rankOf (fun i => E i ω) k = k.val + 1}
      =
    ∫ t in Set.Ioi (0 : ℝ),
      θ k * Real.exp (-(θ k * t)) *
        P.real {ω |
          otherSurvivors (fun i => E i ω) k t
            = n - (k.val + 1)}
```

## Quantifiers, hypotheses, and correspondence

| Lean component | Mathematical meaning and scope |
| --- | --- |
| `{Ω : Type*}` | An arbitrary sample space, in any universe. |
| `[MeasurableSpace Ω]` | The sigma algebra of that sample space. |
| `P : Measure Ω`, `[IsProbabilityMeasure P]` | The common probability measure in both sides of the identity. |
| `n : ℕ` | The finite number of labels. No additional assumption `0 < n` is imposed. |
| `θ : Fin n → ℝ` | All rates, quantified before the clocks and distinguished label. |
| `hθ : ∀ i, 0 < θ i` | Each rate is strictly positive, as in the exponential-clock model. |
| `E : Fin n → Ω → ℝ` | The family of real-valued clocks. |
| `hLaw` | For every label, the clock has law `Exp(θ i)` under `P`; this includes almost-everywhere measurability. |
| `hIndependent` | Joint independence of the entire family under `P`. |
| `k : Fin n` | Any distinguished label. The paper's one-based label is `k.val + 1`. |
| `rankOf ... k = k.val + 1` | Exactly the fixed-point event `R_k = k` after reindexing. |
| `t` | A real integration variable, bound by the integral over `(0,∞)`. |
| `θ k * Real.exp (-(θ k * t))` | The density of the distinguished clock at time `t`. |
| `otherSurvivors ... k t` | The finite indicator sum over exactly the labels other than `k`, using the strict event `E_j > t`. |
| `n - (k.val + 1)` | The paper's `n-k`. The subtraction is nonnegative because `k.val < n`. |

There are exactly two explicit typeclass hypotheses: `MeasurableSpace Ω` and
`IsProbabilityMeasure P`. The standard structures on `ℕ`, `ℝ`, and `Fin n` are
fixed library instances. Classical decidability is used inside the finite-set
definitions; no decidability parameter is added to the theorem.

There is no uniform or existential constant in this lemma. The density's rate
depends only on `θ k`. The domination bound used in the proof is the universal
probability bound `1`.

## Approved representational choices

- `Fin n` uses zero-based labels. Both occurrences of the paper's distinguished
  label are converted to `k.val + 1`. If `n = 0`, there is no `k : Fin n`, so the
  theorem is vacuous without an extra size hypothesis.
- Strict-count rank is defined on every clock vector, including ties. Ties have
  probability zero by a proved atomlessness and independence argument; a
  no-ties hypothesis is not imposed.
- The time integral uses Lebesgue measure restricted to `(0,∞)`. Adding the
  endpoint zero leaves this integral unchanged.
- Probabilities are real-valued via `Measure.real`. Probability measures are
  finite, so conversion from extended nonnegative reals loses no information.
- `HasLaw` permits almost-everywhere measurable clocks. Required predicates on
  clock vectors are proved measurable; law transfer evaluates their preimages
  under `P`. No completeness or stronger measurability assumption is added.
- The theorem is stated on the arbitrary space `Ω`. The canonical exponential
  product space is an intermediate proof construction, not a replacement for
  that interface.

## Proof and dependency inspection

1. Prove the approved finite rank and survivor counts measurable. Joint
   measurability of survivor counts also gives measurability in time of their
   probabilities on the product space.
2. Use the marginal laws and independence to identify the joint clock law with
   the actual product of exponential measures. Transfer probabilities of the
   measurable rank and survivor events between this product law and `P`.
3. Apply `Luce.fixed_point_probability_integral` after the exact finite-set and
   indexing identities. Its proof derives almost-sure absence of ties, splits
   off the distinguished coordinate, applies Tonelli to a nonnegative
   indicator, and uses the exponential density.
4. Separately, `Luce.rank_integrand_integrable` proves integrability of the exact
   approved integrand under exactly the same hypotheses. If `Q(t)` denotes the
   survivor probability, then `0 ≤ Q(t) ≤ 1`, so its density-weighted value is
   dominated by `θ k * exp (-(θ k * t))`. The latter is integrable because
   `θ k > 0`. The equality is therefore accompanied by a proof that its real
   integral is not using Lean's nonintegrable default value.

The transitive project modules inspected are `Model`, `RaceOrder`,
`ExponentialRace`, `ExponentialFacts`, `RankIntegral`, `RankProbability`, and
the new `ApprovedRankIntegral`. Important project dependencies include:

- `Luce.raceRank_eq_iff_survivors`: rank `r` is equivalent to `n-r` survivors
  when the clock vector is injective and `1 ≤ r ≤ n`. The bounds follow from
  the chosen label, and injectivity holds almost surely.
- `Luce.exponentialRace_injective_ae`: the canonical independent exponential
  clocks are injective almost surely, proved from zero diagonal probability.
- `Luce.exponentialRace_disintegrate`: splits the actual product measure into
  the distinguished clock and the remaining clocks, with exponential density.
- `Luce.rank_integral_survivors`, `Luce.rank_integral_real`, and
  `Luce.rank_integral_common`: the conditioning identity, conversion to a real
  integral, and equivalence of the background and common-space probabilities.
- `Luce.fixed_point_probability_integral`: the canonical-space identity for
  label `i.val + 1`, with survivor count `n - i.val` on `Fin (n+1)`.

These are proved project results, not external assumptions. Their source
statements and proofs were inspected; mere successful compilation was not
treated as a statement-equivalence audit. Unrelated algebraic choice-probability
definitions in these files are not used to assert the rank identity.

## Pinned mathlib results used

Lean is `leanprover/lean4:v4.33.1`. Mathlib is `v4.33.1`, commit
`0df444a360eaa60ab8c11dca51a86af692955474`. Neither pin was changed.

All names below were checked against this local mathlib, and their relevant
types are recorded by `audit/RankIntegral.lean`.

| Exact declaration | Module | Relevant statement |
| --- | --- | --- |
| `ProbabilityTheory.HasLaw` | `Mathlib.Probability.HasLaw` | `HasLaw X μ P` contains `AEMeasurable X P` and `P.map X = μ`. |
| `ProbabilityTheory.iIndepFun.hasLaw_pi` | `Mathlib.Probability.HasLaw` | For a finite index type, marginal `HasLaw` assertions and `iIndepFun X P` imply `HasLaw (fun ω i => X i ω) (Measure.pi μ) P`. |
| `ProbabilityTheory.HasLaw.measureReal_eq` | `Mathlib.Probability.HasLaw` | If `HasLaw X μ P` and `{x \| p x}` is measurable, then `P.real {ω \| p (X ω)} = μ.real {x \| p x}`. |
| `measurable_measure_prodMk_left` | `Mathlib.MeasureTheory.Measure.Prod` | For `[SFinite ν]` and measurable `s`, the function `x ↦ ν (Prod.mk x ⁻¹' s)` is measurable. Here s-finiteness follows from the product law being a probability measure. |
| `MeasureTheory.measureReal_le_one` | `Mathlib.MeasureTheory.Measure.Typeclasses.Probability` | For a zero-or-probability measure, `μ.real s ≤ 1`. The probability hypothesis supplies the instance. |
| `integrableOn_exp_mul_Ioi` | `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals` | If `a < 0`, then `IntegrableOn (fun x : ℝ => Real.exp (a*x)) (Set.Ioi c)` for every real `c`. Use `a = -θ k`, `c = 0`. |

## Verification record

`Luce.lean` imports `Luce.ApprovedRankIntegral`, and the default Lake target is
the `Luce` library. Executed checks:

```powershell
lake env lean Luce/ApprovedRankIntegral.lean
lake build
lake env lean Luce/RankIntegralDependencyAudit.lean
lake env lean audit/RankIntegral.lean
```

All exit codes are zero. The default build completed successfully with 3620
jobs. Existing modules report style, unused-variable, and deprecation warnings;
the new theorem module reports no warnings or errors.

Logs:

- `audit/rank-integral-build.txt`: default project build.
- `audit/rank-integral-print.txt`: `#print` of the approved definitions, theorem,
  and integrability companion; axiom reports and mathlib type checks.
- `audit/rank-integral-dependencies.txt`: 38 dependency axiom reports and checks
  of the important project statements.

Source searches over all seven transitive project modules found no `sorry`,
`admit`, declared `axiom`, `native_decide`, `by_contra!`, unsafe or external
implementations, or trust-changing options. The final theorem's transitive
axiom report excludes `sorryAx` and any custom axiom.

## STATEMENT AUDIT

| Field | Result |
| --- | --- |
| Target theorem | `Luce.rank_integral` |
| LaTeX source/label | `fixed_points.tex:835`, `lem:rank-integral`, `eq:rank-integral` |
| Statement changed | NO, relative to the approved statement |
| Hypotheses added | NO |
| Hypotheses strengthened | NO |
| Conclusion weakened | NO |
| Quantifiers changed | NO |
| Constant dependencies changed | NO |
| Definitions mathematically changed | NO |

## TRUST AUDIT

| Field | Result |
| --- | --- |
| New axioms introduced | NO |
| `sorry`/`admit` remaining in dependencies | NO |
| External assumptions used | NO |
| `#print axioms Luce.rank_integral` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms Luce.rank_integrand_integrable` | `[propext, Classical.choice, Quot.sound]` |
| Nonstandard axioms or suspicious dependencies | None found |

These three are standard Lean foundations: propositional extensionality,
classical choice, and quotient soundness.

## BUILD AUDIT

| Field | Result |
| --- | --- |
| Relevant module checked | `Luce/ApprovedRankIntegral.lean`, exit 0 |
| Included in project build | YES, imported by `Luce.lean` |
| `lake build` result | PASS, exit 0, 3620 jobs |
| Dependency and final print audits | PASS, exit 0 |
| Remaining errors | None |

Status: **COMPLETE for this approved lemma only.**
