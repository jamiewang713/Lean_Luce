# Corollary 1.9: Sukhatme permutations

Source: `fixed_points_sampled_profile.tex`, `cor:sukhatme`.

The theorem `Luce.Sukhatme.corollary19` in `Luce/Section1Sukhatme.lean` proves the
independently stated `Luce.Sukhatme.Corollary19` from
`Luce/Section1SukhatmeContract.lean`. The default `Luce/Sections1To7.lean` imports the proof.

## Coverage

The only probabilistic hypotheses are that each row is a measurable random
permutation on a probability space and has the Luce masses for the standard
Sukhatme weights. The spaces may vary with n. There are no input profile,
moment, convergence, or population-estimate assumptions.

| Manuscript assertion | Formal statement |
| --- | --- |
| Standard weights n-i+1 | `weights n` has rate `(n : ℝ) - i.val`, for zero-based `i : Fin n` |
| p(w) = exp(w) exp(-exp(w)) | `density` |
| b_ell = p convoluted ell times, evaluated at 0, divided by ell | `coefficient k`, where ell = k+1 |
| All coefficients are positive and E C_(n,ell) ~ b_ell log n | First probabilistic conclusion of `Corollary19` |
| Joint CLT for lengths 1 through L | Second conclusion, against every bounded continuous test function |
| Fixed-point CLT with coefficient exp(-1) | Third conclusion, with the scalar standard Gaussian law |
| Spatial mean asymptotics and joint independent Gaussian limits | Fourth conclusion, indexed by `Fin L × Fin J` |
| Vanishing expected number of spatial excursions | Final part of the spatial conclusion |
| b_1 = exp(-1) | `coefficient_zero` |
| b_2 = K_0(2) | `coefficient_one` |

The limiting vector law is the product of standard Gaussian measures, so
independence is part of the statement. Spatial counts use the existing
maximum-label root and the actual right-corner distance n-i for zero-based
labels. The reindexing proof removes the singleton active-corner coordinate.

## Proof

`Section1SukhatmeProfile.lean` verifies all power-profile hypotheses for f(x)=1-x,
with an inactive finite left endpoint and right parameters c=beta=eta=1.
It constructs the interior-grid rates by multiplying each row of the
standard weights by 1/(n+1), proves these rates equal f((i+1)/(n+1)), and
uses `Weights.mass_scale` to prove exact equality of the permutation laws.

The proof then specializes `Section6.powerLaw65 .interior` and
`Section6.spatial65 .interior`, the power and spatial components of the
already proved interior-grid extension. It identifies Gamma(2)=1 and all
coefficients explicitly. Projection of the one-coordinate vector gives
the scalar fixed-point CLT. A measure-preserving reindexing gives the
spatial Gaussian law indexed only by cycle length and interval.

`Section1SukhatmeConstants.lean` proves

\[
b_2=\tfrac12\int_{\mathbb R}\exp(-e^w-e^{-w})\,dw
    =\int_0^\infty\exp(-2\cosh w)\,dw=K_0(2).
\]

Mathlib in this project has no modified Bessel K definition. The local
`besselK0` uses the standard positive-real integral representation from
[NIST DLMF 10.32.9](https://dlmf.nist.gov/10.32.E9), specialized to order zero.
The proof establishes integrability at argument 2 and uses evenness to
pass from the whole line to the positive half-line. No special-function
identity is assumed as an axiom.

The manuscript's rounded decimal `0.113894` is not a certified numerical
bound in Lean. The exact identity with K_0(2), and every probabilistic
assertion, are included in the closed theorem.

## Verification

```powershell
lake build Luce.Section1Sukhatme
lake build
lake env lean audit/Section1Sukhatme.lean
```

`audit/Section1Sukhatme.lean` checks the closed theorem, checks the natural-valued
weight formula, prints the statement, and reports dependencies for the main
theorem and its specialization and constant lemmas. Logs are saved as
`audit/sukhatme-build.log`, `audit/sukhatme-library-build.log`, and
`audit/sukhatme-axioms.log`.

All three checks passed with Lean 4.33.1. The full library build completed
successfully (4583 jobs). The main theorem and every audited lemma depend
only on `propext`, `Classical.choice`, and `Quot.sound`; there is no
`sorryAx`, custom axiom, or native-decision axiom. The new modules produce
no warnings; the build replays pre-existing warnings from other modules.
