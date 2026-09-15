# Frozen shell migration contract: assumption audit

Authority: `fixed_points_shell_condition.tex`, not the older manuscript or the migration proposal. Implementation began only after creating `Luce/Section4ShellMigrationContract.lean`. No generalized theorem is certified until the separate closed contract check is proved. The contract remains a proposition, not an axiom or a theorem assertion.

## Permitted data and hypotheses

| Source | Lean content and hidden restrictions |
|---|---|
| Finite model, source `eq:luce-law`, lines 138–172 | `w : WeightArray` abbreviates `(n : ℕ) → Weights n`. `Weights n` has precisely `rate : Fin n → ℝ` and `positive : ∀ i, 0 < rate i`. Thus positivity is required at every finite-row label; no uniform lower or upper rate bound, asymptotic rate restriction, or regularity is in the type. `Fin n` is `{k : ℕ // k < n}`; manuscript label is `k.val+1`. Row zero is empty. |
| `eq:normalization`, lines 215–219 | `NormalizedWeights w` means `∀ n, 0 < n → (1/(n:ℝ)) * ∑ i, (w n).rate i = 1`. Division is real. No normalization is required of the empty row. |
| `ass:profile`, lines 220–239 | `f : ℝ → ℝ` extends the manuscript function outside `(0,1)`, with no restrictions there. `ProfileLimit w f` is exactly `NullMeasurable f profileMeasure ∧ (∀ x ∈ Ioo 0 1, 0 < f x) ∧ ProfileL1Convergence w f`. `profileMeasure = volume.restrict (Ioo 0 1)`. `ProfileL1Convergence` is convergence of the ENNReal `eLpNorm` of the difference to zero at exponent one. This prevents totalized real integration from hiding infinite errors. `stepProfile` is the finite cell sum with `i/n < x ≤ (i+1)/n`; it is zero outside `(0,1]`. No integrability or unit-integral proof is an input. Those are derived in existing Section 3. Lebesgue measurability is the existing approved interpretation of measurable. |
| `ass:fixed-endpoint`, lines 253–280 | Exact definitions in `Section4EndpointShellDefinitions.lean`. Shells have `j ≥ 1`; labels use depth `n-k.val`, so the rate is literally `θ[n,n-m+1]`. Ratios inside `Real.log` are real. A finite minimum is taken only with a proof of nonemptiness. Empty shells have cost zero. The raw iterated limit is ENNReal `Tendsto (fun J => limsup (fun n => ∑' j, if J ≤ j then shellCost w n j else 0) atTop) atTop (𝓝 0)`. No normalization, buffered bound, tightness, or finite intensity is conjoined into it. |
| Arbitrary realization of the finite model | `Ω : ℕ → Type u` is arbitrary at any universe `u`. Every `mΩ n` is any measurable space; `P n` is a measure with the sole instance restriction `IsProbabilityMeasure`, i.e. total mass one. `π n : Ω n → Equiv.Perm (Fin n)` is measurable for the discrete measurable space `⊤` on permutations. `Equiv.Perm` is a bijection with an inverse and inverse identities, not a smaller class of permutations. `hMass` fixes each permutation probability to `Weights.mass`, the product over successive draws of selected rate divided by remaining total rate. No cross-row independence, atomlessness, or special probability-space representation is required. |

The contract quantifies `mΩ` and the probability proofs explicitly and installs them locally only after quantification. It has no ambient mathematical parameters or assumed instances. Universe polymorphism is not a mathematical restriction on the row spaces.

## Removed condition

The historical `EndpointAssumption` is `∃ γ ε₀ : ℝ, ∃ n₀ : ℕ, 0 < γ ∧ 0 < ε₀ ∧ ∀ n ≥ n₀, ∀ k : Fin n, (1-ε₀)*n ≤ k.val+1 → γ ≤ (w n).rate k`. It remains available under the explicit alias `UniformEndpointAssumption`. Existing legacy theorems continue to use it until a shell replacement has actually been proved. It is absent from the new contract.

The new `EndpointShellAssumption` is definitionally the raw limit in the contract. Its sum is a nonnegative extended sum; row finiteness must be proved. This is the literal manuscript limit with extended values before finiteness, rather than a strengthened epsilon definition. No exchange of `J` and `n`, uniform supremum over rows, or rate of convergence has been made.

## Conclusion and representation audit

The full spatial limit and scalar total-variation limit at source lines 318–332 are retained, together with integrability of the literal diagonal density. Definitions used by the conclusion:

- `profileQuantile μ f x` is `Function.invFunOn (profileF μ f) (Ici 0) x`. It assumes no inverse law; the inverse properties, positivity of the denominator, and measurability are proved in Section 3. `profileF = 1-profileH`, `profileH` integrates `exp(-t*f)`, and `profileD` integrates `f*exp(-t*f)` with respect to `profileMeasure`.
- `profileDiagonal f x = rateKernel (profileQuantile profileMeasure f x) (f x) / profileD profileMeasure f (profileQuantile profileMeasure f x)`, with `rateKernel t a = a*exp(-t*a)`. Denominator nonvanishing on the interior is a proved fact, not a typeclass hypothesis. Endpoint extensions affect only Lebesgue-null singleton sets.
- `interiorDensityMeasure f 1 = (volume.restrict (Ioc 0 1)).withDensity (fun x => ENNReal.ofReal (profileDiagonal f x))`. The nonnegative-part convention does not remove negative interior values: `profileDiagonal_nonneg` proves nonnegativity from `ProfileLimit`; the endpoint has zero Lebesgue mass.
- `FinitePointMeasure X` is the subtype of finite nonnegative measures that equal a sum of `m` unit Dirac masses for some `m : ℕ` and map `Fin m → X`. Repeated locations are permitted. Its topology is inherited from the weak topology of finite measures. All bounded continuous real test functions are quantified; no test-dependent convergence hypothesis is supplied.
- `fixedPoints π` is `interiorFixedPoints 1 π`: the sum of unit atoms at `(k.val+1)/n` for fixed labels. Its real-line identity and count identity are already proved. `count` uses the natural floor of an integer-valued mass; the representation lemmas prove equality with the actual finite cardinality.
- `fixedPointCountLaw P π hπ` is the pushforward probability law of that actual count. Measurability of the count is proved, not assumed separately.
- `finitePoissonLaw ν` is the law constructed from a Poisson count of mean `ν.mass` and independent iid locations with law `ν.normalize`, or the zero point measure if `ν=0`. Its probability normalization is proved. `poissonProbabilityMeasure` is the scalar Poisson probability law.
- `probabilityTotalVariation μ ν` is `sSup { |μ.real A - ν.real A| : A ⊆ ℕ }`. On this countable discrete space every subset is measurable; its value lies in `[0,1]` by existing proofs.

`fullIntensity` in the old implementation requires an old endpoint proof to construct a `FiniteMeasure`. The frozen contract instead concludes `∃ ν : FiniteMeasure (Icc 0 1), (ν : Measure _) = (interiorDensityMeasure f 1).map (projIcc 0 1 zero_le_one) ∧ ...`. This is not a new assumption or unspecified limiting law: equality fixes the entire measure. The witness is in the conclusion and must be constructed. A separate representation theorem must identify the old `fullIntensity` with this exact map (its definition makes this a definitional equality). Existing projection-recovery and closed-interval identities justify the original real-line interpretation.

## Existing gaps and proof reuse

The inspected Section 4 main statements have the approved uniform endpoint restriction and the finite model/profile restrictions listed above. No further mathematical antecedent was found in those main types. Helper lemmas may assume integrability, positive denominators, or convergence; only uses that discharge those assumptions from the permitted inputs are acceptable.

The old global low-rate Section 5 proof genuinely uses the uniform endpoint restriction to put every low-rate label into a fixed interior interval. It cannot be reused for shell capacity as written. Lemma 5.2 uses normalization and `ProfileLimit`, without endpoint input. The final joint short-cycle Poisson theorem, factorial-moment completion, and vector total-variation passage were already unfinished. The Section 4 contract check now passes. The new `ProfileLimit.interior_low_rate_cycles_vanish` supplies the revised fixed-interior low-rate truncation under normalization and profile convergence alone. Cycle-shell tightness and the final joint theorem remain unproved; no Section 5 main-theorem completion is claimed.

## Freeze and verification

The freeze recorded SHA256 for the contract, shell definition module, manuscript, and all pre-existing production Lean files and checking configuration. The final comparison checks 162 files and finds no changes. New proof modules and root imports do not alter those definitions. No substantive contract error was found or contract revision made. `section4_contractCheck` proves the original target; its transitive axiom output contains only the three authorized foundational axioms.
