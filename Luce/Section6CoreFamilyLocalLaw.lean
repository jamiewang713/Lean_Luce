import Luce.Section6CoreFamilyDomination
import Luce.Section6NonmoderateFamilies
import Luce.Section6Proposition65

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem PowerProfile.core_family_local_law {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray)
    (hw : SampledRates grid w f) (r : ℕ) :
    ∃ (h0 : ℕ) (delta v d kappa C : ℝ),
      1 ≤ h0 ∧ 0 < delta ∧ 0 < v ∧ 0 < d ∧ 0 < kappa ∧ 0 < C ∧
      ∀ (s n A B : ℕ) (side : Fin s → Corner) (k : Fin s → ℕ),
        Fintype.card (CollisionSlot k) ≤ r →
        (∀ c, (cornerBehavior left right (side c)).active) →
        1 ≤ A → h0 ≤ A → (B : ℝ) ≤ delta*(n : ℝ) →
        ∀ x : CollisionAssignment n A B side k, Function.Injective (collisionLabel x) →
          (∀ p q, p ≠ q → 2*r < Nat.dist (collisionLabel x p).val (collisionLabel x q).val) →
          (∀ p, ¬ cycleEdgeNonmoderate side (fun c => cornerBehavior left right (side c)) k v p x) →
          |coreFamilyRankProbability (w n) x -
            varyingCycleFamilyWeight side k (fun c a b => localIdealKernel (side c)
              (cornerBehavior left right (side c)) (cornerDistance (side c) a) (cornerDistance (side c) b)) x| ≤
            C*((A : ℝ)^(-kappa)+((B : ℝ)/(n : ℝ))^kappa)*
              varyingCycleFamilyWeight side k (fun c a b => localEnvelopeKernel (side c)
                (cornerBehavior left right (side c)) d (cornerDistance (side c) a) (cornerDistance (side c) b)) x := by
  classical
  obtain ⟨h0, delta, v, d, kap, C, hh0, hd, hd1, hv, hv1, hdec, hkap, hC, hlaw⟩ :=
    proposition65_localLaw f left right hp grid w hw r
  refine ⟨h0, delta, v, d, kap, C, hh0, hd, hv, hdec, hkap, hC, ?_⟩
  intro s n A B side k hcard hactive hA hhA hB x hx hsep hmod
  let e := (Fintype.equivFin (CollisionSlot k)).symm
  let u (a : Fin (Fintype.card (CollisionSlot k))) := collisionLabel x (e a)
  let j (a : Fin (Fintype.card (CollisionSlot k))) :=
    collisionLabel x (collisionBlockPermutation k (e a))
  let side' (a : Fin (Fintype.card (CollisionSlot k))) := side (e a).1
  have hu : Function.Injective u := hx.comp e.injective
  have hj : Function.Injective j := hx.comp ((collisionBlockPermutation k).injective.comp e.injective)
  have hlarge (a : Fin (Fintype.card (CollisionSlot k))) :
      h0 ≤ cornerDistance (side' a) (u a) ∧ h0 ≤ cornerDistance (side' a) (j a) :=
    ⟨hhA.trans (x (e a).1 (e a).2).property.1,
      hhA.trans (x (e a).1 (finRotate (k (e a).1+1) (e a).2)).property.1⟩
  have hinterval (a : Fin (Fintype.card (CollisionSlot k))) :
      (A : ℝ) ≤ cornerDistance (side' a) (u a) ∧ (A : ℝ) ≤ cornerDistance (side' a) (j a) ∧
        (cornerDistance (side' a) (u a) : ℝ) ≤ B ∧ (cornerDistance (side' a) (j a) : ℝ) ≤ B := by
    exact ⟨by exact_mod_cast (x (e a).1 (e a).2).property.1,
      by exact_mod_cast (x (e a).1 (finRotate (k (e a).1+1) (e a).2)).property.1,
      by exact_mod_cast (x (e a).1 (e a).2).property.2,
      by exact_mod_cast (x (e a).1 (finRotate (k (e a).1+1) (e a).2)).property.2⟩
  have hmoderate (a : Fin (Fintype.card (CollisionSlot k))) :
      localCornerRatio (side' a) (cornerBehavior left right (side' a))
        (cornerDistance (side' a) (u a)) (cornerDistance (side' a) (j a)) ≤
        (min (cornerDistance (side' a) (u a) : ℝ) (cornerDistance (side' a) (j a) : ℝ))^v :=
    not_not.mp (hmod (e a))
  have hseparated (a b : Fin (Fintype.card (CollisionSlot k))) (hab : a ≠ b) :
      2*r < Nat.dist (j a).val (j b).val := by
    apply hsep
    intro he
    exact hab (e.injective ((collisionBlockPermutation k).injective he))
  have hh := (hlaw n (Fintype.card (CollisionSlot k)) hcard side' u j hu hj
    (fun a => hactive (e a).1) hlarge
    (fun a => ⟨(hinterval a).2.2.1.trans hB, (hinterval a).2.2.2.trans hB⟩)
    hmoderate hseparated).2 (A : ℝ) (B : ℝ)
      (by exact_mod_cast (show 0 < A by omega)) hinterval
  have hprob : {clocks | MarkedRankCylinder u j clocks} =
      {clocks | ∀ p : CollisionSlot k, raceRank clocks (collisionLabel x p) =
        (collisionLabel x (collisionBlockPermutation k p)).val+1} :=
    finite_rank_cylinder_reindex e (collisionLabel x) (fun p => collisionLabel x (collisionBlockPermutation k p))
  have hprod (F : Fin s → Fin n → Fin n → ℝ) :
      (∏ a : Fin (Fintype.card (CollisionSlot k)), F (e a).1 (u a) (j a)) =
      varyingCycleFamilyWeight side k F x := by
    change (∏ a, (fun p : CollisionSlot k => F p.1 (collisionLabel x p)
      (collisionLabel x (collisionBlockPermutation k p))) (e a)) = _
    calc
      _ = ∏ p : CollisionSlot k, F p.1 (collisionLabel x p)
          (collisionLabel x (collisionBlockPermutation k p)) := Equiv.prod_comp e _
      _ = _ := by rw [Fintype.prod_sigma]; rfl
  change |(exponentialRace (w n)).real {clocks | MarkedRankCylinder u j clocks} -
      (∏ a, localIdealKernel (side' a) (cornerBehavior left right (side' a))
        (cornerDistance (side' a) (u a)) (cornerDistance (side' a) (j a)))| ≤
    C*((A : ℝ)^(-kap)+((B : ℝ)/(n : ℝ))^kap)*
      (∏ a, localEnvelopeKernel (side' a) (cornerBehavior left right (side' a)) d
        (cornerDistance (side' a) (u a)) (cornerDistance (side' a) (j a))) at hh
  rw [hprob] at hh
  change |coreFamilyRankProbability (w n) x - _| ≤ _ at hh
  change |coreFamilyRankProbability (w n) x -
    (∏ a, (fun c a b => localIdealKernel (side c) (cornerBehavior left right (side c))
      (cornerDistance (side c) a) (cornerDistance (side c) b)) (e a).1 (u a) (j a))| ≤
    C*((A : ℝ)^(-kap)+((B : ℝ)/(n : ℝ))^kap)*
    (∏ a, (fun c a b => localEnvelopeKernel (side c) (cornerBehavior left right (side c)) d
      (cornerDistance (side c) a) (cornerDistance (side c) b)) (e a).1 (u a) (j a)) at hh
  rw [hprod (fun c a b => localIdealKernel (side c) (cornerBehavior left right (side c))
    (cornerDistance (side c) a) (cornerDistance (side c) b)),
    hprod (fun c a b => localEnvelopeKernel (side c) (cornerBehavior left right (side c)) d
      (cornerDistance (side c) a) (cornerDistance (side c) b))] at hh
  exact hh

end Luce.Section6
