# Section 5: mathematical contract and verification record

**Current status (2026-09-11): the full revised shell-condition Section 5
theorem is proved and audited.** `Luce.section5_main_general` gives literal
cyclic-intensity integrability and the full independent-Poisson vector limit
in weak convergence and total variation on arbitrary finite Luce-law models.
`section5_contractCheck` proves the independently frozen closed contract.
The default build passes, and both declarations depend only on the three
allowed foundational axioms. See [the final report](docs/section5-final-report.md).

The authority for this completed migration is `fixed_points_shell_condition.tex`.
The records below describe earlier work on `fixed_points.tex` and are retained
as history; their unfinished-status statements and old endpoint hypotheses
are superseded by the final shell-condition report.

## Authority and environment

The authority is `fixed_points.tex`, Section 5, **Short cycles**, lines
963–1320. The final result proved there is Theorem 1.4, `thm:short-cycles`,
lines 288–299. `main.tex:3` inputs `fixed_points.tex`. The latter is
self-contained: macros are at 21–32, with no further input/include files.
`commands.tex` and the alternative manuscripts are not inputs to this source.
No mathematical source file is to be edited.

Source SHA256 before implementation:
`0CDC05ACA34BD8E44A949747B815063F969BDD6A4963F650FF1E155B4C6E8E91`.
No applicable AGENTS.md was found in the ancestor chain or project tree
outside dependencies. Existing untracked Lean work is preserved. Existing
`SECTION3_FORMALIZATION.md` is a separate Section 3 work record; because the
request also names it as a deliverable, append a clearly identified Section 5
cross-reference rather than overwrite its Section 3 content.

Pinned environment verified before implementation:

- Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`).
- Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` unchanged.

## Standing definitions and assumptions

The model has strictly positive weights θ[n,i], 1 ≤ i ≤ n (138–162), and
normalization (213–220) n⁻¹Σᵢθ[n,i]=1. Independent exponential clocks of those
rates generate the draw permutation π and its inverse rank permutation R.
The cycle count (164–172) is

    C[n,ell] = (1/ell) sum over injective tuples (i_1,...,i_ell)
                 product_a 1{R(i_a)=i_(a+1)}, i_(ell+1)=i_1.

The factor is 1/ell, not 1/ell!. Ordered collections of cycles in falling
factorials supply no additional m_ell! denominator. Distinct cycles of a
permutation are vertex-disjoint. Inverting a permutation reverses cycles and
preserves their lengths and vertex sets.

Assumption 1.1 (223–229): a Lebesgue-measurable, pointwise positive function
f on (0,1), with ||f_n-f||₁→0; f_n is θ[n,i] on ((i−1)/n,i/n].
Integrability and integral one are consequences, not new hypotheses.
Assumption 1.2 (255–260): ∃γ>0, ε₀>0, n₀, ∀n≥n₀, ∀i,
(1−ε₀)n≤i≤n implies θ[n,i]≥γ. Do not impose ε₀<1.

The transforms (236–248) are H(t)=∫exp(−tf), F=1−H,
D(t)=∫f exp(−tf), t≥0; t_y=F⁻¹(y), and
ρ(x,y)=f(x)exp(−f(x)t_y)/D(t_y). Use t_0=0 (proved inverse endpoint).
Values at x or y equal to 0 or 1 are irrelevant to Lebesgue integrals; the
choice of such values must not change interior values. For ell≥1,

    λ_ell = (1/ell) ∫_[0,1]^ell product_a ρ(x_a,x_(a+1)) dx.

The final theorem includes finiteness of these nonnegative integrals. An
unproved finiteness assertion cannot be hidden by a totalized real integral.

## Exact source results and proposed Lean contracts

The signatures below are specifications, not unproved Lean declarations.
Any named objects not yet implemented have their literal meaning given here.
No signature is claimed checked until its status is recorded below.

### Theorem 1.4, lines 288–299, proved at 1279–1320

Under the standing model, normalization, Assumptions 1.1 and 1.2, for every
fixed nonnegative integer L, (C[n,1],...,C[n,L]) converges jointly to
independent Poisson variables with means λ_1,...,λ_L, both weakly and in
total variation on ℕ^L. L=0 is the singleton empty-vector law.

Proposed fully exposed contract:

```lean
theorem section5_short_cycles
    (w : WeightArray) (f : ℝ → ℝ)
    (hnorm : NormalizedWeights w) (hf : ProfileLimit w f)
    (hend : EndpointAssumption w) (L : ℕ) :
    (∀ ell : ℕ, 0 < ell → cycleIntensityENN f ell < ⊤) ∧
    Tendsto (cycleVectorLaw w L) atTop
      (𝓝 (independentCyclePoissonLaw f L)) ∧
    Tendsto (fun n => totalVariation
      (cycleVectorLaw w L n) (independentCyclePoissonLaw f L))
      atTop (𝓝 0)
```

`cycleVectorLaw w L n` is the pushforward of the actual exponential product
law in row n+1 by the vector of literal cycle counts. Its identification
with the Luce permutation model must be checked, not assumed.
`independentCyclePoissonLaw` is the product of Poisson laws with real
parameters `(cycleIntensityENN f (ell+1)).toReal`; the accompanying strict
finiteness proof prevents the `toReal` convention at infinity from changing
the statement. `cycleIntensityENN` is the nonnegative Lebesgue integral
of the cyclic product divided by ell. Total variation uses the standard
supremum over measurable events (equivalently half the lattice l1 distance).

### Lemma 5.1, moderate reservoir, 977–994

For every α<1, ∃d,η>0, eventually n,
#{i: θ[n,i]≥d}≥(α+2η)n. After any fixed number of deletions and at most αn
arrivals, the remaining rate is at least dηn. All constants are uniform over
the removed labels and the arrival order.

```lean
theorem ProfileLimit.moderate_reservoir
    {w : WeightArray} {f : ℝ → ℝ} (hf : ProfileLimit w f)
    {α : ℝ} (hα : α < 1) :
    ∃ d η : ℝ, 0 < d ∧ 0 < η ∧
      ∀ᶠ n in atTop, (α + 2 * η) * (n : ℝ) ≤
        ((Finset.univ.filter (fun i : Fin n => d ≤ (w n).rate i)).card : ℝ)
```

The same d,η must satisfy, for each m:ℕ, eventually n, for every finite set
`removed : Finset (Fin n)` with `removed.card ≤ α*n+m` (real casts),
`d*η*n ≤ ∑ i ∈ univ \ removed, (w n).rate i`.
Normalization is not used by this proof and may be omitted in this stronger
auxiliary conclusion; it remains a final-theorem hypothesis.

### Lemma 5.2, cyclic local law, 996–1076

For every r≥1, α<1, τ∈S_r and continuous signed real g on [0,α]^r,
the sum in (1000–1006) over injective tuples in [floor(αn)] tends to
∫g(x)∏_aρ(x_a,x_τ(a))dx. Additionally ∃K_(r,α), for every n,
uniformly over injective labels i and injective ranks j≤αn,
P(∀a,R(i_a)=j_a)≤K n^(−r)∏_a θ[n,i_a].

Proposed binders: `(w) (f) (hnorm) (hf) (r : ℕ) (hr : 0 < r)
(α : ℝ) (hα : α < 1) (τ : Equiv.Perm (Fin r))
(g : (Fin r → Set.Icc (0:ℝ) α) → ℝ) (hg : Continuous g)`.
Conclusion is `Tendsto (fun n => cyclicLocalSum w r α τ g n) atTop
(𝓝 (cyclicLocalIntegral f r α τ g))` and the uniformly quantified
inequality above. No regularity on f and no bound on the marked rates in
the final lemma. Bounded rates and separated ranks are auxiliary cutoffs.
For α≤0 the label sets are empty; for α=0 the integral is zero for r≥1.

Translation correction recorded during the focused Lemma 5.2 audit:
the initial specification above said “eventually n” for the weighted
inequality. Source lines 1010–1013 do not state that qualification. The
final contract uses all rows, with one enlarged constant absorbing the
finitely many rows before the reservoir estimate applies. The eventual
version remains a valid auxiliary theorem, not the final specification.

### Ghost windows and Lemma 5.3, 1078–1151

For each fixed ell≥1 use one background family E⁰ and windows
J_j=(T_max(j−ell,0),T_min(j+ell,n+1)), where T_0=0,T_(n+1)=∞.
p_(i,j) is the integral of the rate θ_i exponential density on J_j.
No independence between different windows is asserted.
The ghost cylinder bound (1093–1095) and row bound (1098–1099) are separate
proof obligations. Lemma 5.3: for ell,m≥1, every n and v∈[n],

    E sum over distinct u_0,...,u_(m−1)
        p_(u_0,u_1)...p_(u_(m−1),v) ≤ K_(ell,m).

The endpoint v need not be distinct from the sources. Proposed exact
constant `(2*(ell+m+2)+1)^m` follows the written proof. The measure-preserving
swap must be proved on actual independent copies. A deterministic auxiliary
contract counts paths u with edges `|σ(u)-v|≤q` for any permutation σ:
`pathCount σ q m v ≤ (2*q+1)^m`. Counting all paths before dropping source
distinctness is legitimate only through an injection/subset argument.
Ranks and labels are shifted by one together, so absolute differences agree.
An extra incoming edge gives (1141–1145); repeated sources are separated and
their extra factor removed using 0≤p≤1. For ell=1 this is E c_v≤K.

### Proposition 5.4, exceptional cycles, 1162–1240

For every fixed L:ℕ, under `(w,f,hnorm,hf,hend)`, the two iterated limits
are zero: lim_(M→∞) limsup_n E V_(n,L)({i:θ[n,i]>M})=0 and
lim_(δ↓0) limsup_n E V_(n,L)({i:θ[n,i]<δ})=0.
`V` counts vertices in the specified set that belong to cycles of length
at most L, not cycles and not all vertices of a cycle meeting the set.
Proposed conclusions use `Tendsto` of nonnegative extended-real limsups
along `atTop` and `nhdsWithin 0 (Ioi 0)` respectively, or their exactly
equivalent ε/eventually formulations. No uniform lower bound in the bulk.

### Lemma 5.5, truncated cycle tail, 1245–1277

For every 0<δ<M, every fixed L, under the standing normalized positive
array, the iterated α↑1, limsup_n expectation of the sum of cycles with all
rates in [δ,M] and at least one label >αn is zero. The proof uses only the
normalization; profile and endpoint assumptions are not needed here.
Binders `(w) (hnorm) (δ M : ℝ) (hδ : 0 < δ) (hδM : δ < M) (L : ℕ)`;
limit filter `nhdsWithin 1 (Iio 1)`. Equality cases θ=δ,M are included.
For any finite n with floor(αn)−L≤0, late-order estimates require an explicit
initial-row treatment, not an invalid negative-index order statistic.

## Dictionary and representation safeguards

- `Weights n` has fields `rate : Fin n → ℝ`, `positive : ∀i,0<rate i`.
- `WeightArray`, `NormalizedWeights`, `ProfileLimit`, `EndpointAssumption`
  are the existing definitions in `Luce/Assumptions.lean`, lines 26–99.
  `ProfileLimit` expands to NullMeasurable f on restricted Lebesgue measure,
  pointwise positivity on (0,1), and ENNReal L1-error convergence.
- Paper label i is Lean `Fin n` value i−1. `raceRank` is one-based;
  `clockRank` is zero-based. `rankPermutation` maps label to rank;
  `drawPermutation` is its inverse, not the same map.
- `exponentialRace w = Measure.pi (fun i => expMeasure (w.rate i))`.
  Distinctness of clocks holds almost everywhere, already proved in
  `Luce.ExponentialFacts`; deterministic tie extensions must preserve this law.
- `profileH`, `profileF`, `profileD`, `profileQuantile` are existing literal
  transforms/inverse definitions. Denominator positivity is a theorem.
- A cyclic tuple is an injection from `Fin ell`, with last-to-first successor.
  A cycle object may use mathlib permutation cycles, but correspondence to
  the tuple formula and its factor 1/ell must be proved.
- Nonnegative extended integrals prevent integrability/limit gaps from being
  concealed by totalization. Real integrals require separate integrability.
- Constants in finite path bounds do not depend on n, rates, or endpoint v.
- L=0, n=0, ell=1, and m>n are handled explicitly; no hidden nonemptiness.

## Proof dependency map and hardest obligations

1. 987–993: positive limit profile ⇒ small low-level set; L1 comparison ⇒
   finite-grid reservoir count; subtract arbitrary deletions ⇒ rate bound.
2. 1017–1050: exponential memorylessness and deleted-chain gap representation;
   use the reservoir for uniform cylinder domination; prove separated-gap
   joint asymptotics from the actual race, including uniformity over labels.
   Earlier Lemma 3.1 is in `Section3Race`/`Section3OrderStats`, but its use
   does not by itself prove these microscopic gap asymptotics.
3. 1052–1075: L1 high-rate tails; diagonal-strip bounds; grid-to-integral
   comparison for cyclic products with signed continuous g; ordered limits.
4. 1078–1137: genuine ghost-window containment; conditional product formula;
   independent-copy coordinate swaps preserve the law; finite rank change;
   permutation indegree ≤2q+1 and induction give the insertion-path bound.
5. 1139–1239: added predecessor collision split; high-entry comparison;
   interior window lengths; actual exceptional-cycle expectation estimates.
6. 1257–1276: time-integral cyclic sum with bounded overlap, then normalized
   array order-statistic domination and beta moment. The prose calls this
   moment standard, but it remains a formal dependency if not found/proved.
7. 1279–1298: exact joint falling-factorial expansion with ell-root factors;
   apply the local law and prove factorial-moment determination/tightness
   for independent Poisson limits (not merely assume a convergence criterion).
8. 1300–1319: combine rate truncations and late bounded-rate cycles; derive
   finite cyclic intensities by monotone convergence; Markov cutoff removal;
   countable-lattice pointwise probabilities and Scheffé give total variation.

External mathematical ingredients: exponential memorylessness (existing
local/mathlib results inspected before reuse), finite product integration,
Markov and L1 uniform integrability, beta moments of exponential order
statistics, multivariate factorial-moment convergence, monotone convergence,
and Scheffé. No cited literature theorem is assumed as an interface. Section
5 does not directly apply the stronger local-law criterion mentioned at
198–208; it establishes its own cyclic law and endpoint argument.

The hardest unproved bridge at the initial inspection is the uniform
microscopic cylinder asymptotic (1040–1045), followed by the complete
probabilistic insertion comparison and multivariate factorial-moment limit.
These are not replaceable by new assumptions on the final theorem.

## Delivered proof status

**INCOMPLETE: Theorem 1.4 and Section 5 as a whole are not formalized.**
The contract above was written before implementation and has not been
weakened. No declaration named `section5_short_cycles`, axiom standing in for
it, or conditional replacement for it is supplied. The checked progress includes
two complete numbered lemmas, the high-rate half of Proposition 5.4, cylinder
estimates, and substantive finite combinatorics.

| Source result/step | Checked implementation | Status |
|---|---|---|
| Lemma 5.1, 977–994 | `ProfileLimit.moderate_reservoir_with_remaining_rate` | Fully proved, including deletion consequence |
| Lemma 5.2, 996–1076 | `ProfileLimit.weighted_bulk_cylinder` | Weighted bound fully proved; local asymptotic and signed cyclic integral limit remain |
| Deleted-chain macroscopic estimates, 1035–1038 | `section5_deleted_order_statistics`, `section5_deleted_gap_rate` | Fully proved, uniform over all deletion sets of fixed bounded size; strict post-arrival rates included |
| Windows and finite swaps, 1080–1089, 1121–1135 | `GhostWindowByOrder`, count correspondence, swap measure preservation, path counting | Fully proved |
| Ghost cylinder inequality, 1093–1095 | `ghost_cylinder_bound`, `ghost_cylinder_product_integrable` | Fully proved for actual race law and actual windows |
| Ghost row inequality, 1098–1099 | `ghostEntry_row_bound` | Fully proved |
| Lemma 5.3, 1106–1137 | `finite_insertion_path`, `finite_insertion_path_integrable` | Fully proved, actual real expectation and literal density correspondence |
| Added predecessor, 1139–1151 | `added_predecessor`, `added_predecessor_integrable` | Fully proved, including singleton interpretation and collision multiplicities |
| Proposition 5.4 high rates, 1187–1206 | `ProfileLimit.high_rate_cycles_vanish` | Fully proved, literal iterated limit; half-mass and integrability derived |
| Proposition 5.4 low rates, 1208–1240 | Not yet assembled | Low-rate cycle conclusion remains unproved |
| Profile exceptional-label controls, 1174–1185 | `ProfileLimit.highRateMass_small`, `ProfileLimit.lowRateDensity_small` | Fully proved from the actual L1 profile hypothesis |
| Interior window occupation/length, 1219–1224 | `beforeCount_occupation_le`, `ghostWindowLength_expectation_le`, `ProfileLimit.interior_ghostWindowLength_uniform` | Actual interval bounds, integrability and reservoir discharge; uniform over ell≤L |
| Lemma 5.5, 1245–1277 | None | Unproved |
| Individual cycle formula, 164–172, 303–304 | `Section5.cycleCount_eq_tuple_sum`, inversion and fixed-count identities | Fully proved |
| Collection counting/root factors, 1281–1284 | `rootedCollectionEquivAssignment`, `cycle_factorial_eq_assignment_sum` | Full global labelled-assignment bijection and deterministic factorial expansion proved |
| Bulk cutoff in that expansion, 1281–1295 | `bulk_cycle_factorial_eq_assignment_sum` | Every vertex is restricted to the exact bulk set; arbitrary cutoffs also proved, no invariance assumed |
| Factorial-moment limits and final limit, 1285–1319 | None | Unproved |

All names above without a namespace prefix are in `Luce`; cycle-combinatorics
names are in `Luce.Section5`. `Luce/Section5.lean` is the entry point for all
delivered Section 5 files and is imported by the default `Luce.lean` build.
There is no unfinished Lean proof file excluded to manufacture build success.

### Actual principal theorem types

The following are the checked types in ordinary notation; the audit log also
contains the elaborated types with all implicit arguments made explicit.

```lean
theorem Luce.ProfileLimit.moderate_reservoir_with_remaining_rate
    {w : Luce.WeightArray} {f : ℝ → ℝ}
    (hf : Luce.ProfileLimit w f) {α : ℝ} (hα : α < 1) :
    ∃ d η : ℝ, 0 < d ∧ 0 < η ∧
      (∀ᶠ n : ℕ in Filter.atTop,
        (α + 2 * η) * (n : ℝ) ≤ ((Luce.moderateReservoir w n d).card : ℝ)) ∧
      ∀ m : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∀ removed : Finset (Fin n),
        (removed.card : ℝ) ≤ α * n + m →
          d * η * n ≤ ∑ i ∈ Finset.univ \ removed, (w n).rate i

theorem Luce.finite_insertion_path {n m : ℕ} (w : Luce.Weights n)
    (ell : ℕ) (v : Fin n) :
    (∫ old,
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → Fin n => Function.Injective u),
        ∏ a, Luce.ghostEntry w ell old (u a)
          ((Fin.snoc u v : Fin (m + 1) → Fin n) a.succ)
      ∂Luce.exponentialRace w) ≤ ((2 * (ell + m + 2) + 1) ^ m : ℕ)

-- All mathematical and representational inputs are exposed:
theorem Luce.Section5.cycleCount_eq_tuple_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α) (k : ℕ) :
    (Luce.Section5.cycleCount R k : ℝ) = (1 / (k + 1 : ℝ)) *
      ∑ t : Fin (k + 1) ↪ α, Luce.Section5.cycleAssignmentWeight R k t

theorem Luce.Section5.rootedCycleCollection_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α) (L : ℕ) (m : Fin L → ℕ) :
    Nat.card (Luce.Section5.RootedCycleCollection R L m) =
      (∏ ell : Fin L, (Luce.Section5.cycleCount R ell.val).descFactorial (m ell)) *
        ∏ ell : Fin L, (ell.val + 1) ^ m ell
```

`ghostEntry w ell old i j` is the real value of the exponential measure of
`GhostWindowByOrder old hinj ell j`. `ghostEntry_eq_density_integral` proves
that on an injective nonnegative background this equals exactly
∫_(J_j) θ_i exp(−θ_i t)dt **and proves that density integrable on J_j**.
The kernel is extended by zero on tied backgrounds, which have proved
probability zero. Both independence of coordinates and their exponential
laws are proved for the canonical product measure. Neither injectivity nor
nonnegativity of random clocks is an input to `finite_insertion_path`.

The entire finite path sum is proved integrable by
`finite_insertion_path_integrable`, using the finite nonnegative integral
bound. Individual kernels are in [0,1]. The final real expectation therefore
does not rely on a convention for nonintegrable functions or infinity.toReal.

`Section5.cycleCount R k` counts length **k+1**, a documented index shift to
cover all positive lengths including fixed points. `cycleAssignmentWeight`
is the product of the k consecutive assignment indicators and the closing
indicator. `cycleOrbits` is the finite image of actual periodic orbits as
mathlib lists modulo rotation; this is not a renamed rooted-tuple count.
An explicit equivalence of rooted tuples with vertices of minimal period
k+1 and a fiber-cardinality proof supply the divisor. `CycleCollection`
chooses injectively an ordered list of actual cycles of each length, and
`CycleRoots` chooses one actual vertex in each selected cycle.

## Audit A: proof integrity

`audit/Section5.lean` imports the compiled Section 5 entry point and runs
`#print axioms` on the main results and substantive representation bridges.
The principal reservoir, insertion, integrability, density, and cycle-count
results report exactly:

    [propext, Classical.choice, Quot.sound]

The offset-code injectivity lemma needs only `[propext, Quot.sound]`.
There are no other axiom dependencies in the audited results. In particular,
no admitted proof or additional trusted evaluation contributes to them.

This was supplemented with inspection of the local dependency sources,
including actual definitions and proof bodies. The complete local import
closure is recorded in `audit/section5-local-dependencies.txt`. It includes
the exponential probability/disintegration files, exact Luce prefix and
next-draw laws, Section 3 profile/race/order-statistic results, and every
delivered Section 5 module. A separate text scan of this closure found no admitted proof,
mathematical axiom, unsafe/extern/implemented_by mechanism, or native_decide.
The scan is supplementary; the transitive axiom reports and source review
are the proof audit. Unrelated local files not in this dependency closure
are not being certified by this audit.

## Audit B: statements and representations

The audit file prints every custom object used by the principal types,
and uses `set_option pp.explicit true in #check @...` for all principal
statements. The elaborated types were compared separately with the source.

- Reservoir constants d,η precede the arbitrary deletion allowance m.
  They depend only on the profile array and α, not the removed labels or n.
  `moderateReservoir` expands to `univ.filter (d ≤ rate)`.
- Omitting normalization from Lemma 5.1 is a proved strengthening: its source
  proof uses only positive L1 convergence. Normalization is still a required
  hypothesis of the unproved final contract. α<0 is retained.
- The insertion lemma has only n,m,w,ell,v as mathematical inputs. w exposes
  the required positive rates. It has no normalization/profile assumptions,
  as in Lemma 5.3. The terminal vertex is not included in the injectivity
  requirement. The bound is uniform in n,w,v with the exact source constant.
- The window lower/upper indices, strict inequalities, T_0 and T_(n+1)
  sentinels, label→rank orientation, and zero/one-based shifts were checked.
  Upper infinity is an absent upper bound, not a finite fake endpoint.
- Threshold-count windows agree with open order windows away from finitely
  many times. The exponential law assigns those times zero measure. This
  correspondence, rather than an arbitrary change of window definitions,
  justifies the intermediate representation.
- Distinct-source product probabilities follow from independent copies.
  Changing sources does not change their rates. Dropping source restrictions
  in deterministic path counting is an explicit finite-set inclusion.
- The cycle count handles fixed points and inverse permutations. The exact
  root factor is ell, never ell!, and ordered collections have the product
  falling factorial with no m_ell! denominator. Different selected cycles
  have disjoint vertex sets, including cycles with different lengths.
- The finite path theorem includes m=0 and ell=0 as proved extensions. m=0
  is the single empty tuple/product. For m>n the injective source set is empty.
  The source only needs ell,m≥1. For n=0 there is no v:Fin 0; this does not
  make positive rows vacuous. Cycle lengths exceeding cardinality give zero.
- `section5UnitWeights_assumptions` exhibits a single explicit array satisfying
  normalization, profile convergence, and endpoint assumptions simultaneously:
  every rate is 1, f=1, γ=ε₀=1, n₀=0. It verifies nonvacuity of the standing
  hypotheses without numerics or an assumed existence result.

The resumed implementation also received an independent read-only statement
audit by another proof agent. It inspected the original source and expanded
all new count/window/assignment predicates, including the high-rate iterated
limit, deleted strict rates, arbitrary-cutoff bijection and occupation bound.
It found no mathematical mismatch in the completed results and explicitly
confirmed that the low-rate cycle conclusion and local/Poisson limits remain
unproved. In particular, a finite factorial expansion must not be reported as
factorial-moment convergence, and the occupation estimate supplies no joint
gap independence. The final compiler audit remains separate from this review.

## Exact remaining obligations and source issues

1. Prove the deleted-chain exponential-gap representation (1021–1024)
   and bounded marked-label asymptotic
   (1040–1045). Existing uniform empirical race convergence alone does not
   imply the microscopic asymptotic. In particular, prove uniformity over
   marked labels/ranks and uniform integrability before taking expectations.
   More precisely, conditional on each unmarked elimination permutation,
   establish that `ξ_q=W_q°(T_(q+1)−T_q)` has the product of rate-one
   exponential laws, independent of the permutation. The normalized deleted
   times and strict remaining rates are now controlled by proved theorems;
   they do not supply this joint law or its mixed moments.
   Next prove the exact marked insertion identity with `q_a=j_a−a` after
   sorting prescribed ranks. Separation must imply distinct valid gap indices.
   Finally control the uniform product Taylor remainder using bounds for
   products of rescaled gaps and their squares. No mixed-moment or Taylor
   remainder bound has been added as a theorem hypothesis.
2. Finish rate-tail truncation, near-diagonal tuple counting, and the
   signed test-function grid/integral limit in Lemma 5.2.
3. The ghost cylinder and added-predecessor steps are now proved and are no
   longer unresolved dependencies.
4. Complete the low-rate half of Proposition 5.4: the row-sum estimate for
   cycles whose rates are bounded above, the low/high cycle interaction
   count, and the cutoff limit. Expected interior window lengths and both
   profile tail controls are now proved. The high-rate half is fully proved.
5. Complete the cyclic time-integral estimate (1262–1263), normalized-array
   order-statistic domination, beta-moment bound (1272–1275), and Lemma 5.5.
6. The global labelled-assignment bijection and exact deterministic
   factorial expansion, including arbitrary cutoffs and the actual bulk
   set, are now proved. Derive joint factorial-moment limits using the
   still-unproved local law; the finite counting identity is not a limit theorem.
7. Prove multivariate Poisson convergence from those factorial moments,
   endpoint cutoff removal, finiteness/equality of cyclic intensity integrals,
   and the final lattice Scheffé argument for total variation.

No definite mathematical contradiction was found in these inspected source
arguments. Several prose steps remain substantial unproved formal
dependencies, not new assumptions and not established theorems in this run.
Two source endpoint conventions need explicit treatment when those arguments
are implemented:

- At 1218, β=1−ε₀ can be nonpositive. If ε₀≥1, the endpoint condition bounds
  every rate below by γ eventually, so the low-rate set for δ<γ is empty.
  There is no justification for adding ε₀<1 to the final theorem.
- At 1266–1275, take α>1/2 and n sufficiently large so both the full and the
  rate≤2 subfamily order indices are positive. For k=floor(αn)−L, the beta
  shape includes n−k+1≤n(1−α)+L+2. For L≥1 the fixed extra constants can be
  absorbed in K; L=0 is the trivial empty-vector case. No invalid negative
  or zero-index order statistic may be assumed away silently.

The completed proofs preserve the source mechanisms: positive superlevel/L1
comparison for the reservoir, and independent-copy swaps followed by backward
permutation path counting for insertion. The offset-code injection is an
explicit version of the source's indegree induction. Extended integrals and
cycle rotation quotients are equivalent representations with proved bridges.
For weighted bulk domination, the gap grouping is reorganized as successive
conditional Luce choices, derived from the actual exponential-race law.
Every remaining-set denominator has the reservoir lower bound, giving the
same product of rate factors. This is an equivalent hazard argument for the
domination sublemma; it does not replace or prove the microscopic local law.
The high-rate half follows the paper's density comparison, rooted ghost sum,
added-predecessor estimate, and L1 rate-tail argument in that order.

## Reproduction and actual verification

Run from the existing project directory:

```powershell
lake env lean --version
git -C .lake/packages/mathlib rev-parse HEAD
lake build
lake env lean audit/Section5.lean
```

The version and revision commands returned the pinned values above. The
full default build succeeded with 3768 jobs after integrating the Section 5
entry point. The audit entry point succeeded and produced
`audit/section5-audit.log`, containing the actual transitive axiom reports,
full explicit types, and expanded definitions.

Logs: `audit/section5-full-build.log`, `audit/section5-audit.log`, and
`audit/section5-local-dependencies.txt`. Incremental compiler errors were
resolved using compiler feedback; an earlier failed incremental build is not
reported as a success. The manuscript hash remains the value above and git
reports no changes to mathematical source or pinned dependency files.

Verification executed on 2026-09-10 (the final integration pass is recorded below):

| Command | Actual result |
|---|---|
| `lake env lean Luce/Section5FiniteInsertion.lean` | Exit 0; includes the final row bound; only style warnings |
| `lake build` (output redirected to `audit/section5-full-build.log`) | Exit 0, `Build completed successfully (3768 jobs).` |
| `lake env lean audit/Section5.lean` (output redirected to `audit/section5-audit.log`) | Exit 0; all 65 axiom queries and every explicit-type/definition query completed |
| Local dependency-source scan | No prohibited-term matches; saved in `audit/section5-source-scan.txt` |
| Lean version and mathlib HEAD checks | Unchanged pinned version and revision above |
| Manuscript SHA256 recheck | Identical to the initial hash above |

The initial pass checked the reservoir, insertion paths and basic cycle counting.
The table above includes the resumed cylinder, deletion, high-rate and cutoff
work. The final integration record below accounts for the last window additions.

## Continuation contract: exceptional rates and cylinder bounds

The fixed target remains Theorem 1.4, without additional hypotheses. The next
modules address the actual ghost cylinder (1093–1095), added predecessor
(1139–1151), bulk weighted cylinder (1012–1013), and the high-rate argument in
Proposition 5.4 (1174–1206). Auxiliary statements expose their finite hypotheses:

* For any positive `Weights n`, any injective `u : Fin ell → Fin n`, and any
  targets `j : Fin ell → Fin n`, the actual race probability of
  `∀ a, raceRank clocks (u a) = (j a).val + 1` is at most the expectation of
  `∏ a, ghostEntry w ell old (u a) (j a)`. Target distinctness is unnecessary
  for this upper bound; it is retained wherever the source requires it.
* For `m` distinct path sources avoiding the endpoint, the added-predecessor
  expectation is at most `K(ell,m+1) + m*K(ell,m)`. The source uses `m=ell-1`.
* If `n/2 ≤ ∑ k with θ_k ≤ M, θ_k` and `M < θ_i`, then for every nonnegative
  background, `p_ij ≤ (2*θ_i/n) * ∑ k, p_kj`. Positivity of `n` is proved from
  the exposed index `i : Fin n`; the half-mass hypothesis is subsequently
  derived eventually from normalization and the profile assumption.
* From `ProfileLimit w f` alone, for every `ε>0` there is `M₀>0` such that for
  every `M≥M₀`, eventually in `n`, `(∑ θ_i 1{M<θ_i})/n < ε`.
  This is the quantified high-tail assertion in (1174–1178), not an assumed
  uniform-integrability structure.
* For `ProfileLimit w f`, fixed `ell`, and `α<1`, the interior window
  estimate has `∃K>0, eventually_n, ∀j` with one-based `j≤α*n`, both
  integrability of `|J_j|` and `E|J_j|≤K/n`. The finite occupation premise is
  to be discharged with the existing reservoir lemma, and `j+ell<n` must
  be proved eventually from the fixed margin `1-α`.

These extend the existing dependency map and do not change any target statement.

## Additional checked theorem contracts

The following mathematical inputs are the complete assumptions of the new
principal results (representation details are expanded in the audit file).

```lean
theorem Luce.ProfileLimit.weighted_bulk_cylinder
    {w : Luce.WeightArray} {f : ℝ → ℝ}
    (hf : Luce.ProfileLimit w f) (r : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ i j : Fin r ↪ Fin n,
        (∀ a : Fin r, ((j a).val : ℝ) + 1 ≤ α * n) →
        (Luce.exponentialRace (w n)).real
          {clocks | ∀ a, Luce.raceRank clocks (i a) = (j a).val + 1} ≤
          K / (n : ℝ) ^ r * ∏ a : Fin r, (w n).rate (i a)

theorem Luce.ghost_cylinder_bound {n ell : ℕ} (w : Luce.Weights n)
    (u j : Fin ell → Fin n) (hu : Function.Injective u) :
    (Luce.exponentialRace w).real
      {clocks | ∀ a, Luce.raceRank clocks (u a) = (j a).val + 1} ≤
      ∫ old, ∏ a, Luce.ghostEntry w ell old (u a) (j a) ∂Luce.exponentialRace w

theorem Luce.ProfileLimit.high_rate_cycles_vanish
    {w : Luce.WeightArray} {f : ℝ → ℝ}
    (hf : Luce.ProfileLimit w f) (hnorm : Luce.NormalizedWeights w) (L : ℕ) :
    Filter.Tendsto
      (fun M : ℝ => Filter.limsup (fun n => Luce.highCycleExpectation w L n M)
        Filter.atTop) Filter.atTop (nhds 0)
```

`highCycleExpectation w L n M` is exactly the integral of the number of
vertices `v` with `M < (w n).rate v` and permutation period at most `L`.
`shortCycleVertexCount_eq_filter_period_le` proves that the `Fin L` existential
used by the implementation has exactly this meaning. The count is integrable,
and inverse-permutation invariance is proved. The rank permutation is the
actual race rank map on injective clocks; its arbitrary identity extension
on ties is on a proved null set. The limsup proof derives eventual upper
boundedness explicitly; it cannot use a default limsup of an unbounded sequence.

For the predecessor lemma the complete inputs are `{n m : ℕ}`, positive
`w : Weights n`, `ell : ℕ`, and `v : Fin n`. Its actual integrand is

    sum over injective u:Fin m→Fin n avoiding v,
      c_(snoc u v 0) * product_a p_(u a, snoc u v a.succ),
    c_j = sum_k p_(k,j).

Its bound is the natural number
`predecessorConstant ell m = K(ell,m+1) + m*K(ell,m)`, where
`K(ell,m)=(2*(ell+m+2)+1)^m`. The factor `m` comes from counting exactly
the existing source labels, and the new-label case uses an explicit cons
bijection. The endpoint is allowed to be that new predecessor, as in the paper.

The half-mass premise in the finite high-density bound is discharged by
`ProfileLimit.eventually_moderate_half_mass`; it is absent from the final
high-rate theorem. The endpoint assumption is not used by this high-rate
half and is not added. It remains part of the unchanged Theorem 1.4 contract.

The new deletion processes retain the original normalization by `n`, not
`n-r`. They literally sum arrival indicators or surviving rates over
`univ \\ removed`. `section5_deleted_order_statistics` and
`section5_deleted_gap_rate` control all removed sets with cardinality at most
the fixed `r`, simultaneously. Their complete mathematical assumptions are
`w`, `f`, `NormalizedWeights w`, `ProfileLimit w f`, `r : ℕ`, and `α<1`.
The quantile statement alone does not need normalization. The rates in
`deletedEmpiricalRemaining` use strict survival `t < clocks i`, exactly the
post-arrival convention of `W_q°`. Its difference from the weak-survival rate
is bounded by `maxRate/n` on injective backgrounds, a proved probability-one
event. This removes an endpoint discrepancy; it does not assume it away.

`ProfileLimit.lowRateDensity_small` has only the profile hypothesis and an
arbitrary positive error `ε`; it concludes `∃δ₀>0, ∀0<δ≤δ₀, eventually_n,
card{θ_i<δ}/n<ε`. The exact finite-cell integral identity is proved, including
the empty row. Positivity of the limit is used in dominated convergence of
triangular cutoffs; no positive lower bound on the profile is inserted.

### Full finite factorial expansion and cutoff correspondence

`CycleSlot L m = Σ ell : Fin L, Fin (m ell)` and
`CycleVertex L m = Σ b : CycleSlot L m, Fin (b.1.val+1)` explicitly label
every requested cycle and every vertex within it. `cycleVertex_card` proves
that this domain has exactly `Σell (ell.val+1)*m ell` elements.
`cycleBlockPermutation` rotates each directed block by one.

`rootedCollectionEquivAssignment` is a proved two-sided equivalence between
ordered actual cycles with one chosen root per cycle and a globally injective
map `t` satisfying every edge `R(t x)=t(blockPermutation x)`. The proof derives
injectivity across blocks from cycle disjointness and reconstructs both the
actual cycle and its root from the injection.

`CycleCollectionWithin S C` requires **every vertex** of every selected
cycle to be in `S`. `collectionWithin_iff_assignmentWithin` proves this is
equivalent to `∀x,t x∈S`; it does not require `R(S)⊆S`. Hence both the
collection count and the label restriction in the paper are preserved.
The checked principal identity has these complete inputs:

```lean
theorem Luce.Section5.bulk_cycle_factorial_eq_assignment_sum {n : ℕ}
    (R : Equiv.Perm (Fin n)) (L : ℕ) (m : Fin L → ℕ) (a : ℝ) :
    (∏ ell : Fin L,
      ((Luce.Section5.bulkCycleCount R a ell.val).descFactorial (m ell) : ℝ)) =
      (∑ t : Luce.Section5.CycleVertex L m ↪ Fin n,
        if ∀ x, ((t x).val : ℝ) + 1 ≤ a * n
        then Luce.Section5.cycleBlockIndicator R L m t else 0) /
      ∏ ell : Fin L, ((ell.val + 1 : ℕ) : ℝ) ^ m ell
```

The numerator indicator is literally the product of all prescribed edge
indicators, and `bulkCycleCount` counts actual cycles entirely in the
one-based label set `i≤a*n`. The denominator is proved positive even for
empty collections. There is no `m_ell!` factor. This closes the finite
combinatorial dependency, not the factorial-moment convergence dependency.

### Single-gap occupation estimate

`integrated_rank_crossing_intensity` proves that the time integral of
`Σi θ_i P(t≤E_i and clockBeforeCount(E,t)=k)` is exactly one for an existing
rank `k`. It follows by disintegrating one exponential coordinate, factoring
its survival probability from the deleted count, and using the proved fact
that exactly one label occupies each rank. `beforeCount_occupation_le` then
proves

    ∫_(0,∞) P(clockBeforeCount(E,t)=k) dt ≤ 1/B,

with explicit finite hypotheses `w : Weights(n+1)`, `k<n+1`, `B>0`, and
`∀s, card(s)=n+1-k → B≤Σi∈s θ_i`. This is a finite auxiliary hypothesis;
it is not inserted into Theorem 1.4 or the high-rate conclusion. The reservoir
provides the eventual discharge in `ProfileLimit.interior_ghostWindowLength`.
The occupation theorem gives no independence statement for different gaps.

`ghostWindowVolume` is the Lebesgue measure of the actual open `J_j`, with
zero extension only at tied backgrounds, and `ghostWindowLength` is its real
value. The finite ENNReal expectation bound proves finiteness almost everywhere
and real integrability before conversion. `ProfileLimit.interior_ghostWindowLength`
derives `B=d*η*n>0` by applying the reservoir to the complement of every
possible remaining set. The margin `1-α` proves the finite upper endpoint
eventually, so no infinite terminal window is treated as length zero.
The finite-family theorem chooses one positive constant and one eventual
threshold simultaneously for every `ell≤L`:

```lean
theorem Luce.ProfileLimit.interior_ghostWindowLength_uniform
    {w : Luce.WeightArray} {f : ℝ → ℝ}
    (hf : Luce.ProfileLimit w f) (L : ℕ) {α : ℝ} (hα : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ ell : ℕ, ell ≤ L → ∀ j : Fin n,
        (j.val : ℝ) + 1 ≤ α * n →
          MeasureTheory.Integrable
            (fun old => Luce.ghostWindowLength ell old j) (Luce.exponentialRace (w n)) ∧
          (∫ old, Luce.ghostWindowLength ell old j ∂Luce.exponentialRace (w n)) ≤ K / n
```

This proves the expected-window component used in the low-rate argument.
It does not prove the remaining cycle row-sum bound or high/low interaction.
The first-moment proof is reorganized as a crossing-intensity integral, using
actual exponential disintegration. No memoryless gap law is assumed; the
multi-gap factorization needed for Lemma 5.2 remains unresolved.

## Final verification record for this run

Executed after the last Lean proof change, on 2026-09-10:

* `lake build` — exit 0, **3768 jobs**, including all **21 Section 5 proof
  and entry files** via the default `Luce` target. Actual output:
  `audit/section5-full-build.log`.
* `lake env lean audit/Section5.lean` — exit 0. All **65** transitive axiom
  queries and the full explicit-type and definition queries succeeded.
  Actual output: `audit/section5-audit.log`.
* The permitted axiom sets were checked against all 65 actual reports:
  the principal results use exactly `propext`, `Classical.choice`, and
  `Quot.sound`; offset-code injectivity uses only `propext` and `Quot.sound`.
  No additional axiom appeared, including in the final interior-window theorem.
* The transitive local import closure contains **51 files**, recorded in
  `audit/section5-local-dependencies.txt`, with SHA256 values in
  `audit/section5-local-source-hashes.txt`. An independent file inventory
  confirmed every `Luce/Section5*.lean` file is imported. The supplementary
  source scan found no admitted proof or prohibited trust mechanism.
  `audit/section5-source-audit-summary.txt` records that result.
* `lake env lean --version` and
  `git -C .lake/packages/mathlib rev-parse HEAD` returned Lean **4.33.1**
  and mathlib **0df444a360eaa60ab8c11dca51a86af692955474**, respectively.
  `audit/section5-environment.log` contains the actual values.
* The manuscript SHA256 was rechecked after verification and remains
  `0CDC05ACA34BD8E44A949747B815063F969BDD6A4963F650FF1E155B4C6E8E91`.
  `git diff --name-only -- '*.tex' lean-toolchain lakefile.toml lake-manifest.json`
  produced no output. No mathematical source or dependency version was changed.

The independent statement audit and the kernel/axiom audit are separate;
neither was replaced by the source scan. Existing linter/style warnings are
replayed in builds, but the final commands have no compiler errors.
No Lean proof change was made after this final successful build and audit.

**Completion remains partial.** Theorem 1.4 is not declared or proved.
The exact remaining obligations are Lemma 5.2's joint gap law, marked-gap
insertion identity, uniform mixed moments/Taylor estimate and cyclic integral
limit; the low-cycle row bound, high/low interaction and cutoff limit of
Proposition 5.4; Lemma 5.5; and the factorial-moment, finite-intensity, Poisson
and total-variation convergence arguments. The completed results above are
kernel-checked proofs, not assumptions substituted for those obligations.

## Focused continuation: Lemma 5.2

The current requested target is the whole of Lemma 5.2
(`fixed_points.tex:996–1076`), including its signed continuous test function
and the uniform bound already proved in `ProfileLimit.weighted_bulk_cylinder`.
The original contract and hypotheses above remain fixed. No endpoint
assumption, bounded-rate assumption, or gap independence hypothesis is added
to the target. The earlier verification record applies to the earlier files;
new files require a new build and audit.

The remaining proof is split into the following concrete dependencies:

* An exact joint law of the normalized exponential gaps, on every draw order,
  as the order's Luce mass times the product of rate-one exponential laws.
* An exact insertion identity for separated prescribed ranks: the rank event
  is the product of marked-clock events in the gaps with indices `j_a-a`,
  with zero-based conversion made explicit. Integrating out the marked clocks
  yields the expectation of the product of their actual gap probabilities.
* A global quadratic error for exponential probabilities over finite gaps,
  mixed exponential moments, and passage from the already proved deleted
  time/rate convergence to the uniform microscopic estimate.
* High-rate and near-diagonal removal and the signed cyclic integral limit.

The common analytic representation uses functions `g : (Fin r → ℝ) → ℝ`
continuous on the closed cube, rather than globally continuous functions.
Only their restriction to the cube is used; for a function given on the cube
itself, an arbitrary extension has the same restricted continuity and values.
The density is literally `rateKernel (profileQuantile profileMeasure f y)
(f x) / profileD profileMeasure f (profileQuantile profileMeasure f y)`.
Lebesgue integration uses the positive half-open cube, equal to the closed-cube
integral since the excluded coordinate faces are null. The case `α≤0` must
be discharged separately for `r>0` rather than assumed away.

### Implemented proof of Lemma 5.2

The final entry point is `Luce/Section5Lemma52.lean`, imported by
`Luce/Section5.lean` and therefore by the default project build. The final
names are `Luce.section5_bounded_marked_asymptotic`,
`Luce.section5_cyclic_local`, and `Luce.section5_lemma52`. The last theorem
conjoins the literal cyclic limit and the weighted bound **for every row**.
It does not take a microscopic estimate, moment identity, or independence
claim as a hypothesis.

The actual final statement, with all mathematical assumptions exposed, is:

```lean
theorem Luce.section5_lemma52
    (w : Luce.WeightArray) (f : ℝ → ℝ)
    (hnorm : Luce.NormalizedWeights w) (hf : Luce.ProfileLimit w f)
    (r : ℕ) (hr : 0 < r) (α : ℝ) (hα : α < 1)
    (τ : Equiv.Perm (Fin r)) (g : (Fin r → ℝ) → ℝ)
    (hg : ContinuousOn g (Luce.cyclicBulkCube r α)) :
    Tendsto (fun n => Luce.cyclicRaceSum (w n) α τ g) atTop
      (𝓝 (∫ x in Luce.cyclicBulkCube r α,
        g x * ∏ a, Luce.cyclicProfileDensity f (x a) (x (τ a)))) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ∀ i j : Fin r ↪ Fin n,
        (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
          (Luce.exponentialRace (w n)).real
            {old | ∀ a, Luce.raceRank old (i a) = (j a).val + 1} ≤
              K / (n : ℝ) ^ r * ∏ a, (w n).rate (i a)
```

`Weights n` contains exactly a real rate function and strict positivity of
each rate (source 138–162). `NormalizedWeights` asserts mean one for every
positive row (213–220). `ProfileLimit` expands to Lebesgue measurability,
pointwise positivity on `(0,1)`, and convergence of the extended `L¹` norm
of the literal step-profile error (223–229). No endpoint assumption appears.
The limiting profile's integrability and mean one are proved consequences.

`cyclicBulkCube r α` is `Set.pi Set.univ (fun _ => Set.Icc 0 α)`.
`cyclicRaceSum` is the ordered injective-tuple sum with the cutoff
`(i a).val+1≤α*n`, evaluated at the right cell endpoints `((i a).val+1)/n`.
Its event is the actual exponential-race rank event. An embedding is just
an injective tuple; there is no quotient or factorial factor. In the density
`cyclicProfileDensity f x y`, `x` is the source label coordinate and `y` is
the target rank coordinate. `finiteCyclicDensity` uses the actual finite-row
rate, not an unproved pointwise approximation by `f` at a grid point.

The ambient function representation of `g` is justified by the proved
`exists_cyclic_test_extension`: every continuous function on the source cube
has an extension continuous on that cube and agreeing at every point of
the cube. All evaluations in the sum lie in that cube, and the final
integral is explicitly over it. No continuity or measurability is assumed
away from the cube. `cyclicProfileIntegral_eq_volume` proves equality with
closed-cube Lebesgue integration, and `ProfileLimit.integrable_cyclic_density`
proves integrability of the signed integrand before the final limit is used.

The proof dependencies are now as follows:

| Source proof step | Checked implementation |
| --- | --- |
| Memoryless joint gaps, 1017–1024 | `Section5GapLaw`: restricted-order map law, unconditional product law, selected-coordinate law, and actual rate-times-gap correspondence |
| Sorting and exact insertion, 1025–1032 and 1044–1048 | `Section5MarkedGaps`, `Section5DeletedGaps`, `Section5MarkedGapBridge`, `Section5MarkedSort`: exact event identity, product-law disintegration, deleted count windows equal actual finite gaps, and `q_a+a=j_a` |
| All mixed moments, used at 1044–1048 | `Section5GapMoments`, `Section5GapMomentTransfer`, `Section5GapCoefficient`: integrability, factorial mixed moments, `E Y=1`, `E Y²=2^r`, and Taylor envelope expectation `2r` |
| Uniform Taylor expansion, 1044–1048 | `Section5GapTaylor`, `Section5FiniteTaylor`: global quadratic scalar remainder, product remainder retaining all gap factors, and actual probability error bounded by `(2r/n)(M/b)^(r+1)` |
| Reservoir after deletion, 1025–1029 | `Section5GapReservoir`: all finite compact elimination orders, proved complement identity and cardinality bound, no random-rate hypothesis left |
| Uniform macroscopic coefficient replacement, 1035–1048 | `Section5DeletedRace`, `Section5GapCoefficientLimit`, `Section5MarkedCoefficientLimit`: deleted CDF/time/rate estimates, compact rank modulus, and original prescribed-rank shift at most `r/n` |
| Justified expectation replacement, 1035–1048 | `Section5GapExpectation`, `Section5GapProductExpectation`, `Section5MarkedExpectation`: quantitative bad-event truncation with the actual second moment; scalar-to-product probability bound |
| Uniform microscopic estimate, 1039–1048 | `Section5Microscopic`, `Section5MicroscopicSort`: discharge every analytic premise, then derive gap injectivity and finite endpoints from rank separation and the bulk margin |
| High-rate and near-diagonal removal, 1050–1059 | `Section5CyclicReduction`: exact `r × high-rate mass × mean^(r−1)` bound, all dropped restrictions justified by nonnegativity, and bounded-rate dominated convergence away from null diagonals |
| Grid and profile passage, 1061–1075 | `Section5CyclicAnalytic`: exact multidimensional cell measure and grid-sum identity, integrable telescoping envelope, `L¹` replacement, and signed cyclic density limit |
| Uniform bound for every row, 1007–1013 | `Section5BulkCylinderAll`: finite positive early-row constants combined with the previously proved eventual bound |
| Final assembly | `Section5Lemma52`: microscopic and summation premises discharged, row shift removed, closed-cube Lebesgue integral recovered |

Important endpoint and counting checks are part of these proofs. The initial
gap starts at zero. The terminal infinite gap is excluded by a proved
eventual bulk margin. Sorting permutes source/rank pairs together and
preserves their event and product without a factorial. Equal deleted gap
indices give only an upper bound; the exact insertion identity requires
distinct indices and the microscopic theorem proves that condition from
the stated rank separation. Zero gaps and zero powers are included in the
Taylor and moment lemmas. The closed cube at `α=0` is null for `r>0`, and
the negative-α cube and label sum are empty. The early-row extension treats
`n=0,r=0` explicitly and proves the domain empty when `n=0,r>0`.

There are two proof reorganizations, both within the source's mechanism.
The near-diagonal estimate uses dominated convergence on the same bounded-rate
cell errors and the nullity of geometric diagonals, instead of a separately
quantified `O(ζ)` count. The grid/profile passage uses an integrable product
envelope and `L¹` replacement to organize the same truncation argument.
No extra regularity of `f`, rate bound, spacing condition, or convergence
premise survives in the final theorem. No mathematical gap in Lemma 5.2
was found. The source's phrase about standard exponential rescaled gaps is
implemented with the correct normalization `ξ=WΔ`; the gaps `nΔ` themselves
retain the factor `1/D` supplied in the displayed local formula.

The all-row correction above changes the initial translation, not the paper.
One constant works for the fixed array and all rows, labels and bulk ranks;
the auxiliary `weighted_bulk_cylinder_all` has no `g` or `τ` parameter.
Constants are not asserted uniform across different weight arrays/profiles,
which the source's reservoir argument does not provide.

This focused completion is **Lemma 5.2**, not all of Section 5. The remaining
Section 5 obligations are the low-cycle row bound and high/low interaction
and cutoff passage in Proposition 5.4, Lemma 5.5, and the factorial-moment,
finite-intensity, Poisson and total-variation arguments for Theorem 1.4.
The earlier partial status and verification records describe the work before
this continuation; their list of missing Lemma 5.2 dependencies is superseded.

### Final verification of the completed Lemma 5.2

All commands below were executed successfully on 2026-09-10 from
`D:\princeton\Research\Lean\Lean_luce`. Every listed command exited **0**.

```powershell
lake build > audit/lemma52-full-build.log 2>&1
lake env lean audit/Lemma52.lean > audit/lemma52-audit.log 2>&1
lake env lean audit/Section5.lean > audit/lemma52-section5-audit.log 2>&1
lake env lean audit/Lemma52Proof.lean *> audit/lemma52-proof-audit.log
lake env lean audit/Lemma52StatementCheck.lean *> audit/lemma52-statement-types.log
lake env lean --version
git -C .lake/packages/mathlib rev-parse HEAD
```

The full default build completed with **3790 jobs**, including all **43**
`Luce/Section5*.lean` modules and the final `Luce` entry point. The complete
Section 5 local import closure contains **84 files**; its inventory,
post-build unchanged SHA256 hashes, and coverage results are preserved in
`audit/lemma52-full-local-dependencies.txt`,
`audit/lemma52-full-source-hashes.txt`, and
`audit/lemma52-build-coverage.txt`. There are no omitted Section 5 modules.
The supplementary complete-closure source scan found no admitted proof,
new mathematical axiom, or prohibited trust mechanism.

The focused audit completed **16** actual axiom queries, full explicit types
of the final theorems, and expanded definitions. The aggregate Section 5
audit completed **69** axiom queries and its explicit-type/definition queries.
All reports were checked, including universe annotations, against the three
permitted foundational axioms; no additional axiom occurred. The main
theorems `Luce.section5_bounded_marked_asymptotic`,
`Luce.section5_cyclic_local`, and `Luce.section5_lemma52` each depend on exactly:

```text
[propext, Classical.choice, Quot.sound]
```

**Separate proof audit.** `audit/Lemma52Proof.lean` completed **23** axiom
queries and independently traversed the actual checked declaration types
and bodies: **47,107** transitive declarations, including **707** local Luce
declarations. It confirmed the final declarations are theorems, rejected
additional axioms and unsafe/partial dependencies, and found none. The
Lemma 5.2 local import closure has **72 modules**; their hashes were unchanged
after this audit. Its source-body review includes the joint gap law,
insertion identity, mixed moments, Taylor remainder, expectation passage,
cyclic limit, and all-row bound. See
[`audit/lemma52-proof-audit.md`](audit/lemma52-proof-audit.md).
The read-only environment walker supplies no mathematical proof or oracle.

**Separate statement audit.** `audit/Lemma52StatementCheck.lean` displayed
twelve actual elaborated theorem types and seven custom definitions.
The independent comparison with the manuscript checked all mathematical
binders, the closed-cube test representation, one-based ranks, actual
finite-row rates, source/target orientation, ordered tuples, normalization,
integrability, and endpoint cases. It explicitly confirmed the final
`∃ K > 0, ∀ n` bound after the correction described above. No unresolved
statement mismatch remains. See
[`audit/lemma52-statement-audit.md`](audit/lemma52-statement-audit.md).
This comparison is independent of the clean axiom reports.

The final environment remains Lean **4.33.1**, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`; actual output is in
`audit/lemma52-environment.log`. The final manuscript SHA256 remains
`0CDC05ACA34BD8E44A949747B815063F969BDD6A4963F650FF1E155B4C6E8E91`.
The executed command
`git diff --name-only -- '*.tex' lean-toolchain lakefile.toml lake-manifest.json`
produced no output. Mathematical sources and dependency pins are unchanged.
No proof source changed after the final successful full build and audits.

There are **no remaining obligations for Lemma 5.2**. The other Section 5
obligations listed above remain separate unfinished results.

## Continuation of the remaining Section 5 results (2026-09-11)

The source contracts above remain fixed. The next assembly target is the
low-rate conclusion of Proposition 5.4, source 1208–1240, with parameters
`w`, `f`, `NormalizedWeights w`, `ProfileLimit w f`, `EndpointAssumption w`,
and every `L : ℕ`. Define `lowCycleExpectation w L n δ` by the same actual
vertex-count expectation as `highCycleExpectation`, replacing the strict
high-rate predicate by `(w n).rate v < δ`. The target is
`Tendsto (fun δ : ℝ => limsup (fun n => lowCycleExpectation w L n δ) atTop)
  (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)`.

For the proof at 1225–1237, a cycle avoids a high-rate set precisely when
every vertex in its actual permutation orbit avoids that set. This is a
restriction of the event, not an assumption on the background. Planned
dependencies: a nonnegative matrix row-sum path estimate; the actual bound
`p_(u,v) ≤ M |J_v|` for `θ_u≤M` with finite interior windows; the restricted
ghost-cylinder comparison; a finite orbit-counting inequality charging
at most `L` low vertices to each high vertex; and the already proved
`interior_ghostWindowLength_uniform`, `lowRateDensity_small`, and
`highCycleExpectation_small`. The endpoint assumption places low-rate
labels in an interior interval, including the case its parameter is at
least one. All eventual bounds and limsup finiteness must be discharged.

The later targets remain Lemma 5.5 and Theorem 1.4 with the contracts above;
no new source assumptions or unproved intermediate interfaces are allowed.

### Completed Proposition 5.4

The final entry point is `Luce/Section5ExceptionalLow.lean`, imported by
`Luce/Section5.lean` and the default `Luce` build. It combines the previously
proved high-rate limit with the now-proved low-rate limit. The actual main
statement is:

```lean
theorem Luce.section5_proposition54
    (w : Luce.WeightArray) (f : ℝ → ℝ)
    (hnorm : Luce.NormalizedWeights w) (hf : Luce.ProfileLimit w f)
    (hend : Luce.EndpointAssumption w) (L : ℕ) :
    Tendsto (fun M : ℝ => limsup
      (fun n => Luce.highCycleExpectation w L n M) atTop)
      atTop (𝓝 0) ∧
    Tendsto (fun δ : ℝ => limsup
      (fun n => Luce.lowCycleExpectation w L n δ) atTop)
      (𝓝[>] 0) (𝓝 0)
```

Both expectations count exactly vertices in the respective strict
exceptional-rate sets whose permutation cycles have length at most `L`.
The underlying race law, rank permutation and profile/endpoint assumptions
are unchanged. In particular, no global lower or upper rate bound, endpoint
parameter upper bound, nonempty low-rate set, or extra convergence premise
has been added. The existing constant-one array satisfies all assumptions.

| Source step | New checked dependency |
| --- | --- |
| Closing edge at most `M * length(J_i)`, 1225–1227 | `Section5LowCycleRows`: `ghostWindowVolume_ne_top_of_interior` and `ghostEntry_le_rate_mul_length` (all theorem names are in namespace `Luce`) |
| Sum the other edges with the row bound, 1227–1230 | `forwardPathWeight_sum_le`, `rootedGhostProduct_eq_forward`, `bounded_ghost_cycle_sum_le` |
| Restricted actual cycle probability | `Section5LowCycleProbability`: `exists_bounded_cycle_tail`, `bounded_cycle_probability_le_ghost`, `bounded_cycle_probability_le_window` |
| Discharge every window premise using the profile reservoir, 1219–1230 | `ProfileLimit.bounded_cycle_probability_uniform`, using the previously proved `interior_ghostWindowLength_uniform` |
| Count only cycles avoiding high vertices | `shortCycleVertexCountAvoiding_expectation_le`; actual orbit restriction, positive periods, and the finite union over lengths are proved |
| Charge at most L low vertices per high vertex, 1231–1237 | `Section5ExceptionalInteraction`: `shortCycleVertexCount_le_high_add_avoiding` and its expectation version |
| Endpoint localization and quantitative low bound, 1208–1237 | `ProfileLimit.lowCycleExpectation_bound` |
| Successive high- and low-rate cutoffs, 1238–1240 | `ProfileLimit.lowCycleExpectation_small`, `ProfileLimit.low_rate_cycles_vanish` |
| Full proposition, 1162–1240 | `Luce.section5_proposition54` |

The auxiliary open-path sum includes repetitions. Every factor is
nonnegative, so dropping the original injectivity, avoidance and rate
restrictions is justified explicitly. `Fin.consEquiv` proves the tuple
summation bijection. Factoring the closing edge keeps `k=0` as the genuine
fixed-point case; no rotation or factorial multiplier is introduced.

`OrbitAvoids` means every vertex of the actual periodic orbit avoids the
specified high set. The deterministic charging inequality is proved by a
finite union of high-vertex orbits and the exact equality of orbit cardinality
with minimal period. It does not assume the exceptional sets are disjoint
or invariant. All counts are integrable before expectation inequalities.

The endpoint localization uses `alpha = 1-epsilon0/2`, without adding
`epsilon0<1`. A label of rate below `delta<gamma` must have its one-based
index below `(1-epsilon0)n`; if this is impossible, the low set is empty.
The fixed interior margin proves eventual finite window endpoints. Window
volume is proved finite before `toReal` is used, and the expected length
is supplied by the already checked reservoir/occupation argument. The
uniform constant precedes all labels, lengths through L and eventual rows.

The final cutoff proof chooses M from the high-rate estimate and then delta
from low-rate scarcity. The eventual row threshold follows delta. Both
nonnegativity and eventual boundedness of the inner sequences are proved
before taking real limsups. Thus the real representation is legitimate near
each outer limit, and does not turn unbounded sequences into zero.
There is no substantive proof-strategy deviation or mathematical gap in
this proposition; finite orbit unions and explicit epsilon choices expand
the corresponding sentences of the source proof.

### Verification of Proposition 5.4, 2026-09-11

The following commands were actually executed from the project root and
each exited **0**:

```powershell
lake build > audit/proposition54-full-build.log 2>&1
lake env lean audit/Proposition54.lean > audit/proposition54-statement-types.log 2>&1
lake env lean audit/Proposition54Proof.lean > audit/proposition54-proof-audit.log 2>&1
lake env lean audit/Section5.lean > audit/proposition54-section5-audit.log 2>&1
lake env lean --version
git -C .lake/packages/mathlib rev-parse HEAD
```

The full build completed **3794 jobs**, including all **47** Section 5
modules. The full local closure has **88 files**, with no omitted module
and no post-build hash mismatch. Inventories, hashes and supplementary
source-scan results are saved as `audit/proposition54-full-*` and
`audit/proposition54-build-coverage.txt`; the source scan found no matches.

The separate proof audit traversed **46,029** checked declarations,
including **359** local Luce declarations. It rejected additional axioms
and unsafe/partial dependencies and found none. The final proposition,
low-rate limit and bounded-cycle estimate each have exactly
`[propext, Classical.choice, Quot.sound]` as transitive axioms. The focused
audit's **12**, proof audit's **3**, and aggregate audit's **71** axiom
reports were all checked; no extra axiom occurred. This was not merely
a source-text search.

The separate statement audit inspected nine actual elaborated theorem
types and seventeen expanded definitions/structures against the manuscript.
It checked all binders, strict cutoffs, counting units, original row indices,
null-set extensions, uniform constants, empty cases and iterated-limit order.
See [`audit/proposition54-statement-audit.md`](audit/proposition54-statement-audit.md)
and [`audit/proposition54-proof-audit.md`](audit/proposition54-proof-audit.md).
The two audits are separate checks; no additional agent was used for this
continuation.

Lean remains **4.33.1**, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib remains
`0df444a360eaa60ab8c11dca51a86af692955474`. The manuscript SHA256 is still
`0CDC05ACA34BD8E44A949747B815063F969BDD6A4963F650FF1E155B4C6E8E91`.
The manuscript/dependency-pin diff command produced no output. There were
no applicable AGENTS.md files in the project or ancestor chain. No proof
source changed after the successful full build and audits.

**No obligation remains for Proposition 5.4.** The remaining Section 5
work is Lemma 5.5's truncated cyclic sum and late-order estimate, followed
by the joint factorial-moment limit, truncated Poisson convergence, endpoint
removal, finite intensity and total-variation conclusion of Theorem 1.4.
The previously proved finite factorial-counting identity and Lemma 5.2
remain available dependencies, but that final probabilistic assembly is
not claimed complete.
