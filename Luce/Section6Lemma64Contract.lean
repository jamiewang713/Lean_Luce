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
