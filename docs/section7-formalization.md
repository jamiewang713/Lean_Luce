# Section 7: independent-clock extensions

Source: `fixed_points_sampled_profile.tex`, Section 7, beginning at line 3227
when read initially (line 3229 after an external manuscript edit).
Library entry point: `Luce/Section7.lean`, imported by `Luce.lean`.

## Main result

`Luce.Section7.proposition71` proves the closed statement
`Luce.Section7.GeneralClockTailStatement`, corresponding to
`prop:general-clock-tail` and `eq:general-clock-tail`:

\[
\sum_{m=1}^{M}\Pr(R_{n-m+1}=n-m+1)
\le M e^{-cB}+2\int_s^\infty h(t)\,dt.
\]

The constant is explicitly
`c = (1/2 - exp(-1))/2 > 0`, independent of every model parameter.
The closed statement quantifies the constant before the probability space,
row size, clock densities, and cutoffs.

The assumptions are exactly independent clocks with probability densities,
`1 ≤ M ≤ n`, `B - 1 ≥ 2M`, the actual survival-probability equality
`sum_i P(T_i > s) = B`, and the integrable terminal-density envelope on
`t ≥ s`. The statement spells out measurability, nonnegativity, integrability,
and total integral one as the meaning of a probability density. It assumes
neither positive clock times nor a special distributional shape.

`general_clock_tail` is the reusable version on an arbitrary probability
space. It needs integrability of the envelope only on `(s, infinity)`.
`proposition71` checks this result against the separately frozen closed
statement, using the manuscript's global integrability assumption.

## Definitions and indexing

- `rankOf` and `otherSurvivors` reuse the original project definitions.
- A `Fin n` label `i` represents manuscript label `i.val + 1`.
- `terminalLabel n hn m` has value `n-m` for every `1 ≤ m ≤ n`.
  Its total-function fallback outside the summation range is unused.
- `ClockDensity.law` is Lebesgue measure weighted by the stated density.
- `clockRace` is the product of these laws. `HasLaw` and mutual independence
  transfer its results to the original probability space.
- Integrals from `s` to infinity use `(s, infinity)`; including the endpoint
  gives the same Lebesgue integral.

## Proof and additional statements

| Manuscript component | Checked Lean result |
| --- | --- |
| Independent continuous clocks have no ties | `clockRace_injective_ae` |
| Exact conditioning identity | `general_clock_rank_integral` |
| Integrability of the rank integrand | `rank_integrand_integrable` |
| Early survivor-count Chernoff bound | `survivorProbability_early` |
| Common-sample two-candidate bound | `sum_survivorProbability_le_two` |
| Split at the cutoff and integrate the envelope | `density_integral_bound` |
| Full terminal fixed-point estimate | `proposition71`, `general_clock_tail` |
| Vanishing right-hand side for triangular arrays | `general_clock_tail_tendsto_zero` |
| Population `F`, `d`, inverse time, and candidate density | `populationCDF`, `populationDensity`, `populationQuantile`, `bulkDensity` |
| Candidate density is nonnegative and normalized | `bulkDensityAt_nonneg`, `bulkDensityAt_integral`, `bulkDensity_integral` |
| Exponential specialization of the density ratio | `bulkDensityAt_exponential` |
| Gamma shape one is the exponential law | `gammaDensity_one_law` |
| Common integrable envelope at fixed Gamma shape | `gamma_common_integrable_envelope` |

The rank identity uses product-measure disintegration and the derived
almost-sure absence of ties. Its integrability follows from domination by
the candidate's probability density. The early estimate uses the existing
independent Bernoulli Chernoff theorem. The late estimate uses the existing
deterministic two-candidate theorem on a single common sample.

The triangular-array consequence permits varying row lengths, densities,
and probability spaces. It assumes the explicit upper bound tends to zero
and proves that the terminal sum of fixed-point probabilities tends to zero.

The Gamma envelope is concrete: for shape `a > 0`, rate floor `gamma > 0`,
and `t ≥ a/gamma`, every rate `r ≥ gamma` satisfies
`gammaPDFReal a r t ≤ gammaPDFReal a gamma t`. The right side is proved
integrable with total integral one. This covers all positive real shapes.

`bulkDensityAt` accepts any specified inverse time, so it can be used on a
restricted time range. `populationQuantile` is a chosen inverse on the range
of `populationCDF`; the optional uniqueness theorem uses global strict
monotonicity. Normalization itself requires only a nonzero denominator.

## Scope of the final discussion

The candidate bulk density is a definition, not a microscopic local limit
theorem. Section 7 explicitly leaves Gamma and independent-utility local
laws, compensator convergence, and model-specific longer-cycle truncation
and shell estimates as additional inputs. These are not asserted by the new
Lean results. The references to known Ewens, Mallows, and permuton results
remain contextual citations, rather than new results of this section.

## Reproducible verification

The full default build passed **4,578 jobs**. The dedicated type and
transitive-axiom audit passed for **all 54 named declarations in 11 modules**.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. There are no
unproved placeholders or added axioms in the Section 7 sources.

Both frozen contract hashes match. Every preexisting Lean module is unchanged,
and `Luce.lean` has exactly the new Section 7 import. The toolchain and
dependency inputs also match their starting hashes.

The combined preservation validator reports **failed** solely because
`fixed_points_sampled_profile.tex` changed externally during the run. The
Section 7 text was compared with the initial tool output and still matches,
including Proposition 7.1, its proof, the bulk-density discussion, and the
Gamma example. This task did not edit the manuscript. The initial hash
baseline is preserved; the mismatch is not waived or reset. This source
preservation result is separate from the passing build and proof audit.

```powershell
lake build *> audit/section7-full-build.log
python audit/generate_section7_audit.py
lake env lean audit/Section7.lean *> audit/section7-audit.log
python audit/generate_section7_audit.py --validate
```

The validator reads saved output from `audit/section7-full-build.log` and
`audit/section7-audit.log`. The dedicated audit prints the full types and
transitive axioms of all named Section 7 definitions and theorems. It checks
for unproved placeholders, forbidden axioms, changes to the frozen statement,
and changes to all preexisting Lean sources, the manuscript, and toolchain
inputs. `Luce.lean` is allowed only the additional Section 7 import.

The machine-readable result is `audit/section7-validation.json`.
