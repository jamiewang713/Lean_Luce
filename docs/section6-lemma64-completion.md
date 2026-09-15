# Lemma 6.4: completion evidence

The full frozen Lemma 6.4 proposition is proved, including its matrix and literal cycle-count components. This is not a claim about later Section 6 lemmas or any main CLT.

## Statement and assumption audit

The source is fixed_points_sampled_profile.tex, Assumption ass:simple-power-profile (line 385), Lemma lem:sp-domination (line 2141), and its stated fixed-index estimates. The complete hypothesis/type audit is in docs/section6-lemma64-contract.md. The exact closed contract below was frozen before the combined proof. All 45 files in its project import/source/configuration snapshot remain unchanged.

REMOVED mathematical inputs: none. ADDED mathematical inputs: none. OTHER mathematical input or conclusion changes: none. The old uniform-endpoint-to-shell replacement belongs to Sections 4 and 5; neither endpoint predicate nor normalization is an assumption of this Section 6 lemma.

The only model antecedents are the original positive continuous sampled power profile and exact sampling. Constants, cutoffs, matrix, and positive exponents are constructed outputs. Both sampling grids are covered; midpoint specializes to the manuscript. Fin n is the zero-based representation of labels 1,...,n; right depth is n-i.val; cycle length is k+1. Probability, rank, cycle, maximum-root, and discarded-count meanings are unchanged.

## Actual fully elaborated theorem types and axiom output

```lean
theorem Luce.Section6.lemma64 : Luce.Section6.Lemma64Contract.lemma64 :=
⋯
'Luce.Section6.lemma64' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

```lean
theorem Luce.Section6.lemma64_contractCheck : Luce.Section6.Lemma64Contract.lemma64 :=
Luce.Section6.lemma64
'Luce.Section6.lemma64_contractCheck' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

```lean
theorem Luce.Section6.lemma64_matrix : Luce.Section6.Lemma64Contract.matrix :=
⋯
'Luce.Section6.lemma64_matrix' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

```lean
theorem Luce.Section6.lemma64_cycles : Luce.Section6.Lemma64Contract.cycles :=
⋯
'Luce.Section6.lemma64_cycles' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

These are closed types: no additional explicit, implicit, universe, or instance parameters occur. The audit used pp.explicit, pp.universes and pp.fullNames. All 650 Section 6 declarations have transitive axiom reports containing only propext, Classical.choice and Quot.sound. No sorryAx or project axiom occurs.

## Complete closed contract (unchanged source)

```lean
import Luce.Section6DiscardedCountDefinitions
import Luce.Section5GhostCylinder
import Luce.Section5CycleProbability
import Luce.Section6ExceptionalSums

/-! Independent closed targets for the entire manuscript Lemma 6.4.
No implementation theorem or assumed proof-input predicate occurs here.
The matrix is existential output, not additional model data or an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace Luce.Section6.Lemma64Contract

def matrix : Prop :=
  ∀ (f : ℝ → ℝ) (left right : EndpointBehavior), PowerProfile f left right →
  ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
  ∀ r : ℕ,
  ∃ (M : (n : ℕ) → Fin n → Fin n → ℝ) (C delta kappa v : ℝ)
    (d nu : Corner → ℝ) (H : Corner → ℕ),
    0 < C ∧ 0 < delta ∧ delta < 1 ∧ 0 < kappa ∧ 0 < v ∧ v ≤ 1 ∧
    (∀ side, 0 < d side ∧ 0 < nu side ∧ 1 ≤ H side) ∧
    (∀ n (i j : Fin n), 0 ≤ M n i j) ∧
    (∀ n t, t ≤ r → ∀ u j : Fin t → Fin n, Injective u → Injective j →
      (exponentialRace (w n)).real {clocks | MarkedRankCylinder u j clocks} ≤
        C * ∏ a, M n (u a) (j a)) ∧
    (∀ n (i : Fin n), (∑ j, M n i j) ≤ C) ∧
    (∀ n (j : Fin n), delta*(n : ℝ) ≤ (j.val : ℝ)+1 →
      (j.val : ℝ)+1 ≤ (1-delta)*(n : ℝ) →
      (∀ i, M n i j ≤ C/(n : ℝ)) ∧ (∑ i, M n i j) ≤ C) ∧
    (∀ c alpha eta : ℝ, left = .power c alpha eta →
      (∀ n (j : Fin n), ((j.val : ℝ)+1)/(n : ℝ) ≤ delta →
        (∀ i, M n i j ≤ C/((j.val : ℝ)+1)) ∧ (∑ i, M n i j) ≤ C) ∧
      (∀ n (i : Fin n),
        (∑ j, (((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa*M n i j) ≤ C) ∧
      (∀ n (i j : Fin n), H .left ≤ j.val+1 →
        ((i.val : ℝ)+1)/(n : ℝ) ≤ delta → ((j.val : ℝ)+1)/(n : ℝ) ≤ delta →
        M n i j ≤ C*(((((j.val : ℝ)+1)/((i.val : ℝ)+1))^alpha/((j.val : ℝ)+1))*
          Real.exp (-d .left*(((j.val : ℝ)+1)/((i.val : ℝ)+1))^alpha)+
          exceptionalEnvelope alpha v (d .left) (nu .left) (j.val+1) (i.val+1))) ∧
      (∀ n (i j : Fin n), j.val+1 ≤ H .left →
        M n i j ≤ C*((w n).rate i/(n : ℝ)^alpha))) ∧
    (∀ c beta eta : ℝ, right = .power c beta eta →
      (∀ n (j : Fin n), (cornerDistance .right j : ℝ)/(n : ℝ) ≤ delta →
        (∀ i, M n i j ≤ C/(cornerDistance .right j : ℝ)) ∧ (∑ i, M n i j) ≤ C) ∧
      (∀ n (i : Fin n),
        (∑ j, ((cornerDistance .right j : ℝ)/(cornerDistance .right i : ℝ))^kappa*M n i j) ≤ C) ∧
      (∀ n (i j : Fin n), H .right ≤ cornerDistance .right j →
        (cornerDistance .right i : ℝ)/(n : ℝ) ≤ delta →
        (cornerDistance .right j : ℝ)/(n : ℝ) ≤ delta →
        M n i j ≤ C*((((cornerDistance .right i : ℝ)/(cornerDistance .right j : ℝ))^beta/
          (cornerDistance .right j : ℝ))*
          Real.exp (-d .right*((cornerDistance .right i : ℝ)/(cornerDistance .right j : ℝ))^beta)+
          exceptionalEnvelope beta v (d .right) (nu .right)
            (cornerDistance .right i) (cornerDistance .right j))) ∧
      (∀ n (i j : Fin n), cornerDistance .right j ≤ H .right →
        M n i j ≤ C*Real.exp (-d .right*(cornerDistance .right i : ℝ)^nu .right)) ∧
      (∀ n (i j : Fin n), cornerDistance .right j ≤ H .right →
        delta*(n : ℝ) ≤ (cornerDistance .right i : ℝ) →
        M n i j ≤ C*Real.exp (-d .right*(n : ℝ)^nu .right)))

def cycles : Prop :=
  ∀ (f : ℝ → ℝ) (left right : EndpointBehavior), PowerProfile f left right →
  ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
  ∀ k : ℕ, ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    (∀ n (v : Fin n), delta*(n : ℝ) ≤ (v.val : ℝ)+1 →
      (v.val : ℝ)+1 ≤ (1-delta)*(n : ℝ) →
      (∫ clocks, ((Finset.univ.filter (fun c : ↥(Section5.cycleOrbits (raceRankPermutation clocks) k) =>
        Section5.cycleMaximum (raceRankPermutation clocks) k c = v)).card : ℝ)
        ∂exponentialRace (w n)) ≤ C/(n : ℝ)) ∧
    (∀ side : Corner, (cornerBehavior left right side).active →
      (∀ n (v : Fin n), (cornerDistance side v : ℝ)/(n : ℝ) ≤ delta →
        (∫ clocks, ((Finset.univ.filter (fun c : ↥(Section5.cycleOrbits (raceRankPermutation clocks) k) =>
          Section5.cycleMaximum (raceRankPermutation clocks) k c = v)).card : ℝ)
          ∂exponentialRace (w n)) ≤ C/(cornerDistance side v : ℝ)) ∧
      (∀ (n : ℕ) (A B : ℝ), B/(n : ℝ) ≤ delta →
        (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) side k A B : ℝ)
          ∂exponentialRace (w n)) ≤ C))

/-- The full lemma: the same matrix has every stated property, together
with the literal rooted-count and discarded-count expectation conclusions. -/
def lemma64 : Prop := matrix ∧ cycles

end Luce.Section6.Lemma64Contract

```

## Fully elaborated closed contract definitions (actual Lean output)

```lean
def Luce.Section6.Lemma64Contract.matrix : Prop :=
∀ (f : Real → Real) (left right : Luce.Section6.EndpointBehavior),
  Luce.Section6.PowerProfile f left right →
    ∀ (grid : Luce.Section6.SamplingGrid) (w : Luce.WeightArray),
      Luce.Section6.SampledRates grid w f →
        ∀ (r : Nat),
          ∃ M C delta kappa v d nu H,
            And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                C)
              (And
                (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  delta)
                (And
                  (@LT.lt.{0} Real Real.instLT delta
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                  (And
                    (@LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) kappa)
                    (And
                      (@LT.lt.{0} Real Real.instLT
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) v)
                      (And
                        (@LE.le.{0} Real Real.instLE v
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                        (And
                          (∀ (side : Luce.Section6.Corner),
                            And
                              (@LT.lt.{0} Real Real.instLT
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (d side))
                              (And
                                (@LT.lt.{0} Real Real.instLT
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (nu side))
                                (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (H side))))
                          (And
                            (∀ (n : Nat) (i j : Fin n),
                              @LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (M n i j))
                            (And
                              (∀ (n t : Nat),
                                @LE.le.{0} Nat instLENat t r →
                                  ∀ (u j : Fin t → Fin n),
                                    @Function.Injective.{1, 1} (Fin t) (Fin n) u →
                                      @Function.Injective.{1, 1} (Fin t) (Fin n) j →
                                        @LE.le.{0} Real Real.instLE
                                          (@MeasureTheory.Measure.real.{0} (Fin n → Real)
                                            (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a =>
                                              Real.measurableSpace)
                                            (@Luce.exponentialRace n (w n))
                                            (@Set.ofPred.{0} (Fin n → Real) fun clocks =>
                                              @Luce.MarkedRankCylinder n t u j clocks))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                                            (∏ a, M n (u a) (j a))))
                              (And (∀ (n : Nat) (i : Fin n), @LE.le.{0} Real Real.instLE (∑ j, M n i j) C)
                                (And
                                  (∀ (n : Nat) (j : Fin n),
                                    @LE.le.{0} Real Real.instLE
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta
                                          (@Nat.cast.{0} Real Real.instNatCast n))
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                          (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n j))
                                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                                      @LE.le.{0} Real Real.instLE
                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                            (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n j))
                                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                              delta)
                                            (@Nat.cast.{0} Real Real.instNatCast n)) →
                                        And
                                          (∀ (i : Fin n),
                                            @LE.le.{0} Real Real.instLE (M n i j)
                                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                (@instHDiv.{0} Real
                                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                C (@Nat.cast.{0} Real Real.instNatCast n)))
                                          (@LE.le.{0} Real Real.instLE (∑ i, M n i j) C))
                                  (And
                                    (∀ (c alpha eta : Real),
                                      @Eq.{1} Luce.Section6.EndpointBehavior left
                                          (Luce.Section6.EndpointBehavior.power c alpha eta) →
                                        And
                                          (∀ (n : Nat) (j : Fin n),
                                            @LE.le.{0} Real Real.instLE
                                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                  (@instHDiv.{0} Real
                                                    (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                    (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n j))
                                                    (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                      (@One.toOfNat1.{0} Real Real.instOne)))
                                                  (@Nat.cast.{0} Real Real.instNatCast n))
                                                delta →
                                              And
                                                (∀ (i : Fin n),
                                                  @LE.le.{0} Real Real.instLE (M n i j)
                                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                      (@instHDiv.{0} Real
                                                        (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                      C
                                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                        (@instHAdd.{0} Real Real.instAdd)
                                                        (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n j))
                                                        (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                          (@One.toOfNat1.{0} Real Real.instOne)))))
                                                (@LE.le.{0} Real Real.instLE (∑ i, M n i j) C))
                                          (And
                                            (∀ (n : Nat) (i : Fin n),
                                              @LE.le.{0} Real Real.instLE
                                                (∑ j,
                                                  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@HPow.hPow.{0, 0, 0} Real Real Real
                                                      (@instHPow.{0, 0} Real Real Real.instPow)
                                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                        (@instHDiv.{0} Real
                                                          (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                          (@instHAdd.{0} Real Real.instAdd)
                                                          (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n i))
                                                          (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                            (@One.toOfNat1.{0} Real Real.instOne)))
                                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                          (@instHAdd.{0} Real Real.instAdd)
                                                          (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n j))
                                                          (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                            (@One.toOfNat1.{0} Real Real.instOne))))
                                                      kappa)
                                                    (M n i j))
                                                C)
                                            (And
                                              (∀ (n : Nat) (i j : Fin n),
                                                @LE.le.{0} Nat instLENat (H Luce.Section6.Corner.left)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Fin.val n j)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  @LE.le.{0} Real Real.instLE
                                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                        (@instHDiv.{0} Real
                                                          (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                          (@instHAdd.{0} Real Real.instAdd)
                                                          (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n i))
                                                          (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                            (@One.toOfNat1.{0} Real Real.instOne)))
                                                        (@Nat.cast.{0} Real Real.instNatCast n))
                                                      delta →
                                                    @LE.le.{0} Real Real.instLE
                                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                          (@instHDiv.{0} Real
                                                            (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                            (@instHAdd.{0} Real Real.instAdd)
                                                            (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n j))
                                                            (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                              (@One.toOfNat1.{0} Real Real.instOne)))
                                                          (@Nat.cast.{0} Real Real.instNatCast n))
                                                        delta →
                                                      @LE.le.{0} Real Real.instLE (M n i j)
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul) C
                                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                            (@instHAdd.{0} Real Real.instAdd)
                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                              (@instHMul.{0} Real Real.instMul)
                                                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                (@instHDiv.{0} Real
                                                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                                (@HPow.hPow.{0, 0, 0} Real Real Real
                                                                  (@instHPow.{0, 0} Real Real Real.instPow)
                                                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                    (@instHDiv.{0} Real
                                                                      (@DivInvMonoid.toDiv.{0} Real
                                                                        Real.instDivInvMonoid))
                                                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                      (@instHAdd.{0} Real Real.instAdd)
                                                                      (@Nat.cast.{0} Real Real.instNatCast
                                                                        (@Fin.val n j))
                                                                      (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                        (@One.toOfNat1.{0} Real Real.instOne)))
                                                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                      (@instHAdd.{0} Real Real.instAdd)
                                                                      (@Nat.cast.{0} Real Real.instNatCast
                                                                        (@Fin.val n i))
                                                                      (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                        (@One.toOfNat1.{0} Real Real.instOne))))
                                                                  alpha)
                                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                  (@instHAdd.{0} Real Real.instAdd)
                                                                  (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n j))
                                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                    (@One.toOfNat1.{0} Real Real.instOne))))
                                                              (Real.exp
                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                  (@instHMul.{0} Real Real.instMul)
                                                                  (@Neg.neg.{0} Real Real.instNeg
                                                                    (d Luce.Section6.Corner.left))
                                                                  (@HPow.hPow.{0, 0, 0} Real Real Real
                                                                    (@instHPow.{0, 0} Real Real Real.instPow)
                                                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                      (@instHDiv.{0} Real
                                                                        (@DivInvMonoid.toDiv.{0} Real
                                                                          Real.instDivInvMonoid))
                                                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                        (@instHAdd.{0} Real Real.instAdd)
                                                                        (@Nat.cast.{0} Real Real.instNatCast
                                                                          (@Fin.val n j))
                                                                        (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                          (@One.toOfNat1.{0} Real Real.instOne)))
                                                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                        (@instHAdd.{0} Real Real.instAdd)
                                                                        (@Nat.cast.{0} Real Real.instNatCast
                                                                          (@Fin.val n i))
                                                                        (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                          (@One.toOfNat1.{0} Real Real.instOne))))
                                                                    alpha))))
                                                            (Luce.Section6.exceptionalEnvelope alpha v
                                                              (d Luce.Section6.Corner.left)
                                                              (nu Luce.Section6.Corner.left)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) (@Fin.val n j)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1))))
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) (@Fin.val n i)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1))))))))
                                              (∀ (n : Nat) (i j : Fin n),
                                                @LE.le.{0} Nat instLENat
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Fin.val n j)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                    (H Luce.Section6.Corner.left) →
                                                  @LE.le.{0} Real Real.instLE (M n i j)
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul) C
                                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                        (@instHDiv.{0} Real
                                                          (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                        (@Luce.Weights.rate n (w n) i)
                                                        (@HPow.hPow.{0, 0, 0} Real Real Real
                                                          (@instHPow.{0, 0} Real Real Real.instPow)
                                                          (@Nat.cast.{0} Real Real.instNatCast n) alpha)))))))
                                    (∀ (c beta eta : Real),
                                      @Eq.{1} Luce.Section6.EndpointBehavior right
                                          (Luce.Section6.EndpointBehavior.power c beta eta) →
                                        And
                                          (∀ (n : Nat) (j : Fin n),
                                            @LE.le.{0} Real Real.instLE
                                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                  (@instHDiv.{0} Real
                                                    (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                  (@Nat.cast.{0} Real Real.instNatCast
                                                    (@Luce.Section6.cornerDistance Luce.Section6.Corner.right n j))
                                                  (@Nat.cast.{0} Real Real.instNatCast n))
                                                delta →
                                              And
                                                (∀ (i : Fin n),
                                                  @LE.le.{0} Real Real.instLE (M n i j)
                                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                      (@instHDiv.{0} Real
                                                        (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                      C
                                                      (@Nat.cast.{0} Real Real.instNatCast
                                                        (@Luce.Section6.cornerDistance Luce.Section6.Corner.right n
                                                          j))))
                                                (@LE.le.{0} Real Real.instLE (∑ i, M n i j) C))
                                          (And
                                            (∀ (n : Nat) (i : Fin n),
                                              @LE.le.{0} Real Real.instLE
                                                (∑ j,
                                                  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@HPow.hPow.{0, 0, 0} Real Real Real
                                                      (@instHPow.{0, 0} Real Real Real.instPow)
                                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                        (@instHDiv.{0} Real
                                                          (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                        (@Nat.cast.{0} Real Real.instNatCast
                                                          (@Luce.Section6.cornerDistance Luce.Section6.Corner.right n
                                                            j))
                                                        (@Nat.cast.{0} Real Real.instNatCast
                                                          (@Luce.Section6.cornerDistance Luce.Section6.Corner.right n
                                                            i)))
                                                      kappa)
                                                    (M n i j))
                                                C)
                                            (And
                                              (∀ (n : Nat) (i j : Fin n),
                                                @LE.le.{0} Nat instLENat (H Luce.Section6.Corner.right)
                                                    (@Luce.Section6.cornerDistance Luce.Section6.Corner.right n j) →
                                                  @LE.le.{0} Real Real.instLE
                                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                        (@instHDiv.{0} Real
                                                          (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                        (@Nat.cast.{0} Real Real.instNatCast
                                                          (@Luce.Section6.cornerDistance Luce.Section6.Corner.right n
                                                            i))
                                                        (@Nat.cast.{0} Real Real.instNatCast n))
                                                      delta →
                                                    @LE.le.{0} Real Real.instLE
                                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                          (@instHDiv.{0} Real
                                                            (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                          (@Nat.cast.{0} Real Real.instNatCast
                                                            (@Luce.Section6.cornerDistance Luce.Section6.Corner.right n
                                                              j))
                                                          (@Nat.cast.{0} Real Real.instNatCast n))
                                                        delta →
                                                      @LE.le.{0} Real Real.instLE (M n i j)
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul) C
                                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                            (@instHAdd.{0} Real Real.instAdd)
                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                              (@instHMul.{0} Real Real.instMul)
                                                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                (@instHDiv.{0} Real
                                                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                                (@HPow.hPow.{0, 0, 0} Real Real Real
                                                                  (@instHPow.{0, 0} Real Real Real.instPow)
                                                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                    (@instHDiv.{0} Real
                                                                      (@DivInvMonoid.toDiv.{0} Real
                                                                        Real.instDivInvMonoid))
                                                                    (@Nat.cast.{0} Real Real.instNatCast
                                                                      (@Luce.Section6.cornerDistance
                                                                        Luce.Section6.Corner.right n i))
                                                                    (@Nat.cast.{0} Real Real.instNatCast
                                                                      (@Luce.Section6.cornerDistance
                                                                        Luce.Section6.Corner.right n j)))
                                                                  beta)
                                                                (@Nat.cast.{0} Real Real.instNatCast
                                                                  (@Luce.Section6.cornerDistance
                                                                    Luce.Section6.Corner.right n j)))
                                                              (Real.exp
                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                  (@instHMul.{0} Real Real.instMul)
                                                                  (@Neg.neg.{0} Real Real.instNeg
                                                                    (d Luce.Section6.Corner.right))
                                                                  (@HPow.hPow.{0, 0, 0} Real Real Real
                                                                    (@instHPow.{0, 0} Real Real Real.instPow)
                                                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                      (@instHDiv.{0} Real
                                                                        (@DivInvMonoid.toDiv.{0} Real
                                                                          Real.instDivInvMonoid))
                                                                      (@Nat.cast.{0} Real Real.instNatCast
                                                                        (@Luce.Section6.cornerDistance
                                                                          Luce.Section6.Corner.right n i))
                                                                      (@Nat.cast.{0} Real Real.instNatCast
                                                                        (@Luce.Section6.cornerDistance
                                                                          Luce.Section6.Corner.right n j)))
                                                                    beta))))
                                                            (Luce.Section6.exceptionalEnvelope beta v
                                                              (d Luce.Section6.Corner.right)
                                                              (nu Luce.Section6.Corner.right)
                                                              (@Luce.Section6.cornerDistance Luce.Section6.Corner.right
                                                                n i)
                                                              (@Luce.Section6.cornerDistance Luce.Section6.Corner.right
                                                                n j)))))
                                              (And
                                                (∀ (n : Nat) (i j : Fin n),
                                                  @LE.le.{0} Nat instLENat
                                                      (@Luce.Section6.cornerDistance Luce.Section6.Corner.right n j)
                                                      (H Luce.Section6.Corner.right) →
                                                    @LE.le.{0} Real Real.instLE (M n i j)
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul) C
                                                        (Real.exp
                                                          (@HMul.hMul.{0, 0, 0} Real Real Real
                                                            (@instHMul.{0} Real Real.instMul)
                                                            (@Neg.neg.{0} Real Real.instNeg
                                                              (d Luce.Section6.Corner.right))
                                                            (@HPow.hPow.{0, 0, 0} Real Real Real
                                                              (@instHPow.{0, 0} Real Real Real.instPow)
                                                              (@Nat.cast.{0} Real Real.instNatCast
                                                                (@Luce.Section6.cornerDistance
                                                                  Luce.Section6.Corner.right n i))
                                                              (nu Luce.Section6.Corner.right))))))
                                                (∀ (n : Nat) (i j : Fin n),
                                                  @LE.le.{0} Nat instLENat
                                                      (@Luce.Section6.cornerDistance Luce.Section6.Corner.right n j)
                                                      (H Luce.Section6.Corner.right) →
                                                    @LE.le.{0} Real Real.instLE
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul) delta
                                                          (@Nat.cast.{0} Real Real.instNatCast n))
                                                        (@Nat.cast.{0} Real Real.instNatCast
                                                          (@Luce.Section6.cornerDistance Luce.Section6.Corner.right n
                                                            i)) →
                                                      @LE.le.{0} Real Real.instLE (M n i j)
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul) C
                                                          (Real.exp
                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                              (@instHMul.{0} Real Real.instMul)
                                                              (@Neg.neg.{0} Real Real.instNeg
                                                                (d Luce.Section6.Corner.right))
                                                              (@HPow.hPow.{0, 0, 0} Real Real Real
                                                                (@instHPow.{0, 0} Real Real Real.instPow)
                                                                (@Nat.cast.{0} Real Real.instNatCast n)
                                                                (nu Luce.Section6.Corner.right)))))))))))))))))))))
def Luce.Section6.Lemma64Contract.cycles : Prop :=
∀ (f : Real → Real) (left right : Luce.Section6.EndpointBehavior),
  Luce.Section6.PowerProfile f left right →
    ∀ (grid : Luce.Section6.SamplingGrid) (w : Luce.WeightArray),
      Luce.Section6.SampledRates grid w f →
        ∀ (k : Nat),
          ∃ C delta,
            And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                C)
              (And
                (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  delta)
                (And
                  (@LT.lt.{0} Real Real.instLT delta
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                  (And
                    (∀ (n : Nat) (v : Fin n),
                      @LE.le.{0} Real Real.instLE
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta
                            (@Nat.cast.{0} Real Real.instNatCast n))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n v))
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                        @LE.le.{0} Real Real.instLE
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n v))
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) delta)
                              (@Nat.cast.{0} Real Real.instNatCast n)) →
                          @LE.le.{0} Real Real.instLE
                            (@MeasureTheory.integral.{0, 0} (Fin n → Real) Real Real.normedAddCommGroup
                              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                              (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
                              (@Luce.exponentialRace n (w n)) fun clocks =>
                              @Nat.cast.{0} Real Real.instNatCast
                                (@Finset.card.{0}
                                  ↥(@Luce.Section5.cycleOrbits.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
                                      (@Luce.raceRankPermutation n clocks) k)
                                  {c |
                                    @Eq.{1} (Fin n)
                                      (@Luce.Section5.cycleMaximum n (@Luce.raceRankPermutation n clocks) k c) v}))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) C
                              (@Nat.cast.{0} Real Real.instNatCast n)))
                    (∀ (side : Luce.Section6.Corner),
                      (Luce.Section6.cornerBehavior left right side).active →
                        And
                          (∀ (n : Nat) (v : Fin n),
                            @LE.le.{0} Real Real.instLE
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@Nat.cast.{0} Real Real.instNatCast (@Luce.Section6.cornerDistance side n v))
                                  (@Nat.cast.{0} Real Real.instNatCast n))
                                delta →
                              @LE.le.{0} Real Real.instLE
                                (@MeasureTheory.integral.{0, 0} (Fin n → Real) Real Real.normedAddCommGroup
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
                                  (@Luce.exponentialRace n (w n)) fun clocks =>
                                  @Nat.cast.{0} Real Real.instNatCast
                                    (@Finset.card.{0}
                                      ↥(@Luce.Section5.cycleOrbits.{0} (Fin n) (Fin.fintype n) (instDecidableEqFin n)
                                          (@Luce.raceRankPermutation n clocks) k)
                                      {c |
                                        @Eq.{1} (Fin n)
                                          (@Luce.Section5.cycleMaximum n (@Luce.raceRankPermutation n clocks) k c) v}))
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) C
                                  (@Nat.cast.{0} Real Real.instNatCast (@Luce.Section6.cornerDistance side n v))))
                          (∀ (n : Nat) (A B : Real),
                            @LE.le.{0} Real Real.instLE
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) B
                                  (@Nat.cast.{0} Real Real.instNatCast n))
                                delta →
                              @LE.le.{0} Real Real.instLE
                                (@MeasureTheory.integral.{0, 0} (Fin n → Real) Real Real.normedAddCommGroup
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                                  (@MeasurableSpace.pi.{0, 0} (Fin n) (fun a => Real) fun a => Real.measurableSpace)
                                  (@Luce.exponentialRace n (w n)) fun clocks =>
                                  @Nat.cast.{0} Real Real.instNatCast
                                    (@Luce.Section6.intervalDiscardedCycleCount n (@Luce.raceRankPermutation n clocks)
                                      side k A B))
                                C)))))
def Luce.Section6.Lemma64Contract.lemma64 : Prop :=
And Luce.Section6.Lemma64Contract.matrix Luce.Section6.Lemma64Contract.cycles

```

## Proof and obligation discharge

The complete current ledger is docs/section6-obligation-ledger.md. Section6Lemma64Matrix constructs M from the actual insertion domination matrix at order r+1. It derives the left envelope, right cutoff and endpoint target/column cutoff, intersects those cutoffs, then obtains the right decay and interior estimates at the FINAL cutoff. It constructs the common weighted exponent and chooses C=1+L+R+T+W+B+I+J. Every helper premise is discharged by the profile, sampling, or already proved numeric positivity. Section6Lemma64Cycles constructs its count bounds from exact count/indicator identities and the proved endpoint and interior expectation estimates. No Lemma 6.4 estimate remains an assumed input.

## Commands and actual results

- Individual Lean compilation of Section6ActiveEnvelopes and Section6Lemma64Matrix: exit 0 after fixing elaboration errors; no statement edits.
- lake build Luce.Section6Lemma64Audit: exit 0, 4064 jobs (audit/section6-lemma64-contract-build.log).
- lake build: exit 0, 4266 jobs (audit/section6-progress-build.log).
- python audit/generate_section6_current_audit.py: 650 source declarations.
- lake env lean audit/Section6Current.lean: exit 0 (audit/section6-current-audit.log).
- python audit/freeze_section6_lemma64_contract.py: 45 frozen files, changed=[].
- python audit/validate_section6_progress.py: FAILED at line 21 on the older manuscript hash, after passing declaration-set and axiom-whitelist checks.

## Preserved historical limitation

The original 13-file Section 6 freeze still differs at fixed_points_sampled_profile.tex. It was not reset or repaired; its old manuscript contents are unavailable. The later independent 45-file Lemma 6.4 freeze, created before the combined proof, passes. This report does not claim the old global validator passed, nor that the full historical manuscript is unchanged. The current source assumption and complete Lemma 6.4 statement were reread and compared against the frozen contract. Later density/trace/collision arguments and main CLTs remain outside this completion claim.
