# Assumptions 1.1 and 1.2

Source: `fixed_points.tex`, Section 1. Both numbered assumptions and the shared
definitions are implemented in `Luce/Assumptions.lean`. The user approved the
Lebesgue interpretation of “measurable” in Assumption 1.1 on 2026-09-10.
The definitions below record that approved formulation.

## Shared model and normalization

The manuscript specifies positive weights at line 139. `Luce.WeightArray` is
`(n : ℕ) → Luce.Weights n`, reusing the existing positive-weight structure.
The paper's label `k` is represented by a `Fin n` element with value `k - 1`.
The empty row `n = 0` imposes no weight or endpoint condition and contributes
only an initial zero step profile to the limit sequence.

`eq:normalization`, lines 215–217, states

\[
\frac1n\sum_{i=1}^n\theta_{n,i}=1.
\]

It is encoded separately, without folding it into either numbered assumption:

```lean
def NormalizedWeights (w : WeightArray) : Prop :=
  ∀ n : ℕ, 0 < n → (1 / (n : ℝ)) * (∑ i : Fin n, (w n).rate i) = 1
```

`eq:step-profile`, lines 219–221, uses the exact cells
`(i-1)/n < x ≤ i/n`. `stepProfile w n x` is the finite sum of the weights times
the indicators of these left-open/right-closed cells. In zero-based Lean
indexing, the cell is `i.val / n < x ≤ (i.val + 1) / n`. The definition preserves
the values at every grid point. Its value outside `(0,1]` is zero.

`profileMeasure` is `volume.restrict (Set.Ioo (0 : ℝ) 1)`.

## Assumption 1.1: exact source and implemented predicate

`fixed_points.tex:223`, label `ass:profile`, equation `eq:L1-profile`:

```latex
\begin{assumption}\label{ass:profile}
There is a measurable $f:(0,1)\to(0,\infty)$ such that
\begin{equation}\label{eq:L1-profile}
 \lVert f_n-f\rVert_{L^1(0,1)}\longrightarrow0.
\end{equation}
In particular, $\int_0^1f=1$.
\end{assumption}
```

The implemented convergence clause is:

```lean
def ProfileL1Convergence (w : WeightArray) (f : ℝ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => eLpNorm (fun x => stepProfile w n x - f x) 1 profileMeasure)
    atTop (𝓝 0)
```

For exponent 1 this extended seminorm is the nonnegative integral of the
absolute error on `(0,1)`. Infinite errors stay infinite. No real Bochner
integral is used as a surrogate for the norm of a nonintegrable function.

The approved Lebesgue formulation is implemented as follows:

```lean
def ProfileLimit (w : WeightArray) (f : ℝ → ℝ) : Prop :=
  NullMeasurable f profileMeasure ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x) ∧
    ProfileL1Convergence w f

def ProfileAssumption (w : WeightArray) : Prop :=
  ∃ f : ℝ → ℝ, ProfileLimit w f
```

`NullMeasurable` means measurability with respect to completed Lebesgue measure
on the interval. Values of the real-domain function outside `(0,1)` are
unconstrained and irrelevant. Positivity is pointwise on the entire interval,
as required by the source's positive codomain; it is not weakened to
almost-everywhere positivity.

The user selected Lebesgue measurability after the distinction from Borel
measurability was explained. The definition therefore uses the completed
measure's measurable sets, without choosing a Borel representative of `f`.

| Clause | Meaning |
| --- | --- |
| `w : WeightArray` | The given positive triangular weight array. |
| `∃ f : ℝ → ℝ` | A single limiting profile, restricted mathematically to `(0,1)`. |
| `NullMeasurable f profileMeasure` | Lebesgue measurability on the profile domain, as approved. |
| `∀ x ∈ Set.Ioo 0 1, 0 < f x` | Strict positivity at every point of the domain. |
| `ProfileL1Convergence w f` | The entire sequence of step profiles converges to this same `f` in `L¹(0,1)`. |

All structures on `ℝ`, `ℕ`, and `Fin n` are fixed standard instances. No generic
typeclass hypotheses or extra measurability/finiteness assumptions are hidden
in these predicates. The uses of classical decidability inside the finite
step-profile definition do not add a parameter to the assumptions.

The existential profile depends on the weight array and is chosen before the
limit over row sizes. No integrability or unit-integral hypothesis is added.
Integrability follows from finite step profiles and this norm convergence;
the phrase “In particular, integral f = 1” is a consequence using normalization.
Those consequences are not yet proved in this new module and are not asserted
as axioms or fields. The displayed L1 convergence is retained; it is not
replaced by full-sequence almost-everywhere convergence.

## Assumption 1.2: exact source and implemented predicate

`fixed_points.tex:255`, label `ass:endpoint`, equation `eq:endpoint-lower`:

```latex
\begin{assumption}\label{ass:endpoint}
There are $\gamma>0$, $\eps_0>0$, and $n_0$ such that
\begin{equation}\label{eq:endpoint-lower}
 \theta_{n,k}\ge\gamma
 \quad\text{whenever }n\ge n_0\text{ and }(1-\eps_0)n\le k\le n.
\end{equation}
\end{assumption}
```

```lean
def EndpointAssumption (w : WeightArray) : Prop :=
  ∃ γ ε₀ : ℝ, ∃ n₀ : ℕ,
    0 < γ ∧ 0 < ε₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ k : Fin n,
        (1 - ε₀) * (n : ℝ) ≤ (k.val : ℝ) + 1 →
          γ ≤ (w n).rate k
```

| Clause | Meaning |
| --- | --- |
| `w : WeightArray` | The given positive triangular weight array. |
| `∃ γ ε₀, ∃ n₀` | Constants and a threshold chosen once for the array. |
| `0 < γ ∧ 0 < ε₀` | Exactly the two strict positivity conditions in the source. |
| `∀ n, n₀ ≤ n` | The same witnesses work for every sufficiently large row. |
| `∀ k : Fin n` | All valid labels; `1 ≤ k.val + 1 ≤ n` is inherent in the index type. |
| `(1 - ε₀) * n ≤ k.val + 1` | The inclusive lower boundary in the source. |
| `γ ≤ (w n).rate k` | The uniform lower bound on the selected terminal weights. |

There are no additional typeclass parameters, measurability, integrability,
boundedness, or finiteness hypotheses. The array is finite in each row as in
the paper. The witnesses may depend on the array, but not on the later `n` or
`k`. There is no assumption `ε₀ ≤ 1`.

The predicate does not assert that an arbitrary array satisfies Assumption 1.2.
It can be used as an explicit hypothesis in a later theorem.

## Pinned mathlib inspection

Lean and mathlib remain at version 4.33.1. Relevant exact declarations:

- `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`, module
  `Mathlib.MeasureTheory.Function.LpSeminorm.Defs`:
  `eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ`.
- `MeasureTheory.NullMeasurable`, module
  `Mathlib.MeasureTheory.Measure.NullMeasurable`:
  `∀ ⦃s⦄, MeasurableSet s → NullMeasurableSet (f ⁻¹' s) μ`.
  Its `measurable'` declaration views the function as measurable on
  `NullMeasurableSpace`, the completed measurable space.

## STATEMENT AUDIT

- Target definitions: `ProfileAssumption` / `ProfileLimit` and
  `EndpointAssumption`, together with `NormalizedWeights`, `stepProfile`,
  `profileMeasure`, and `ProfileL1Convergence`.
- LaTeX sources/labels: `eq:normalization`, `eq:step-profile`, `eq:L1-profile`,
  `ass:profile` at line 223, and `ass:endpoint` / `eq:endpoint-lower` at line 255
  in `fixed_points.tex`.
- Statement changed: NO, relative to the approved Lebesgue formulation.
- Hypotheses added: NO.
- Hypotheses strengthened: NO.
- Conclusion weakened: NO.
- Quantifiers changed: NO; zero-based indexing and the empty initial row are
  the implementation conventions described above.
- Constant dependencies changed: NO.
- Existing definitions mathematically changed: NO.
- Full `ass:profile` predicate: implemented with the approved measurability clause.

## TRUST AUDIT

- New axioms introduced: NO.
- `sorry` / `admit` remaining in implemented definitions' dependencies: NO.
- External assumptions used: NO.
- Each implemented definition's `#print axioms` result:
  `[propext, Classical.choice, Quot.sound]`.
- No nonstandard axioms or suspicious dependencies found.

Source checks covered the new module and its only project dependency, `Model`.
Defining the `ProfileAssumption` and `EndpointAssumption` predicates introduces
no axiom asserting that either predicate holds for an array.

## BUILD AUDIT

- Relevant module checked: `lake env lean Luce/Assumptions.lean`, exit 0.
- Included in the project build: YES, imported by `Luce.lean`.
- `lake build`: PASS, exit 0, 3621 jobs.
- `lake env lean audit/Assumptions.lean`: PASS, exit 0; runs `#print` and
  `#print axioms` on the implemented definitions.
- Remaining errors: none in the checked module or build. Existing modules have
  linter warnings.

Logs: `audit/assumptions-module.txt`, `audit/assumptions-build.txt`, and
`audit/assumptions-print.txt`.

Status: **Both Assumption 1.1 and Assumption 1.2 are formalized as predicates.**
The unit-integral consequence of Assumption 1.1 plus normalization remains a
separate theorem to formalize; it is not claimed as proved here.
