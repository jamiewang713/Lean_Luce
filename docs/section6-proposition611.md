# Proposition 6.11: the adapted Bernoulli central limit criterion

The manuscript result is **Proposition 6.11**, label
`prop:sp-fixed-martingale`, in `fixed_points_sampled_profile.tex`.
Its complete statement is proved by `Luce.Section6.proposition611`, with
the independent `proposition611_contractCheck`. Both are imported through
`Luce.Section6` and the default `Luce` target.

## Statement and assumptions

The closed statement in `Section6Proposition611Contract.lean` takes finite
adapted Boolean rows, the project's established encoding of zero-one
observations. Their conditional probabilities are derived using conditional
expectation, with clipping that changes only null exceptional sets. Row
lengths and probability spaces may vary with n; empty rows are allowed.

The only asymptotic assumptions are the manuscript's:

- v tends to infinity;
- (sum p - v) / sqrt(v) tends to zero in probability;
- sum p^2 / v tends to zero in probability.

The conclusion is convergence of expectations against **every bounded
continuous real test function** to its integral under `gaussianReal 0 1`.
There is no independence hypothesis, deterministic cap, extra moment
assumption, or positivity hypothesis for the finitely many initial v values.
The optional expectation premise is used only for the expectation conclusion.

The underlying `BernoulliCLT.boundedContinuous_tendsto` also supports arbitrary
universe levels and directly accepts a `BernoulliProcess` with its actual
conditional-expectation identity.

## Proof

The implementation uses the characteristic-function proof discussed before
implementation, without invoking a general martingale central limit theorem.

1. Apply the existing predictable deletion with atom cap 1 and total
   compensator cap 2v. The capped row agrees with the original when sum p <= 2v.
   The first probability hypothesis shows that deletion has vanishing probability.
2. Write u = t/sqrt(v), a = exp(iu)-1, and
   Z_m = exp(iu S_m - a A_m) for each prefix of the capped row.
   The conditional Bernoulli identity gives the exact expected one-step factor
   exp(-ap)(1+ap). Its error from 1 is bounded by 3|ap|^2.
3. Telescope the expectations. The cap gives the deterministic bound
   |Z_m| <= exp(4t^2), and the total error is at most a constant depending
   on t times E[sum p^2/v]. The capped ratio lies in [0,2], so its convergence
   in probability implies convergence in L1. No L1 convergence is assumed
   for the original, uncapped row.
4. Compare exp(a A - iuv) with exp(av - iuv). A bounded complex exponential
   comparison uses precisely (A-v)/sqrt(v) -> 0 in probability. The third-order
   exponential remainder proves av-iuv -> -t^2/2.
5. Remove deletion, handle the finitely many nonpositive initial normalizers
   by eventual equality with max(1,v), and apply mathlib's proved Levy
   convergence theorem to the actual pushforward probability measures.
6. The expectation assertion follows from the exact tower-property identity
   E[sum I] = E[sum p].

## Modules

| Module | Content |
|---|---|
| `BernoulliCharacteristicEstimates` | Complex exponential remainder and coefficient bounds |
| `BernoulliCharacteristic` | Prefix sums, measurability, integrability, exact conditional identity |
| `BernoulliCharacteristicDrift` | Finite-row accumulated expectation error |
| `ComplexProbabilityConvergence` | Bounded complex expectation comparisons on varying spaces |
| `BernoulliGaussianScale` | Gaussian exponent and characteristic-function limit |
| `BernoulliCLTStopping` | Cap preservation, square-sum domination, vanishing deletion probability |
| `BernoulliCLTCapped` | Characteristic-function convergence of capped rows |
| `BernoulliCLT` | Uncapped criterion and full weak convergence |
| `Section6Proposition611` | Finite-row bridges and complete manuscript proposition |

## Verification

Completed validation: the full default build passed (4466 jobs), and all
55 new theorem declarations passed the type and transitive-axiom audit.
The closed contract hash is unchanged. No proof placeholders or checking
bypasses were found in the eleven new modules.

Run `python audit/validate_section6_proposition611.py` from the project root.
It checks the unchanged pre-implementation contract hash, scans all eleven new
Lean modules for proof placeholders and checking bypasses, runs the full default
build, and prints every new theorem's type and transitive axioms. The permitted
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

The generated audit is `audit/Section6Proposition611.lean`; the machine-readable
results and source hashes are in `audit/section6-proposition611-validation.json`.
Build and axiom output are preserved in the corresponding log files. Historical
Section 6 audit generators and baselines are unchanged.

This completes the generic Proposition 6.11 criterion. Applying it to prove
the critical-pole theorem still requires the model-specific compensator
estimates. The power-law and spatial cycle CLTs are separate obligations.
