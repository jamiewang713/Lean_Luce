import Luce.Section6CoreFamilyLocalLaw
import Luce.Section6CoreFamilyComparison
import Luce.Section6CoreFamilyBadSet
import Luce.Section6FactorialDominationData
import Luce.Section6FiniteKernelBounds
import Luce.Section6FactorialCoreCutoffs
import Luce.Section6FactorialErrorAlgebra

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

/-- Quantitative comparison of labelled core families, uniform in arbitrary
deterministic restrictions on individual cycles. -/
theorem PowerProfile.core_family_quantitative {f : ℝ → ℝ} {left right : EndpointBehavior}
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray)
    (hw : SampledRates grid w f) {s : ℕ} (side : Fin s → Corner) (k : Fin s → ℕ)
    (hactive : ∀ c, (cornerBehavior left right (side c)).active) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ P : ∀ c, (Fin (k c+1) → Fin n) → Prop,
      |(∑ x : CollisionAssignment n (idealCoreLower n) (idealCoreUpper n) side k,
          coreFamilyActualWeight side k P (w n) x) -
        (∑ x : CollisionAssignment n (idealCoreLower n) (idealCoreUpper n) side k,
          coreFamilyIdealWeight side (fun c => cornerBehavior left right (side c)) k P x)| ≤
        C*(1+Real.log (n : ℝ))^(s+1)*(idealCoreLower n : ℝ)^(-eta) := by
  classical
  let r := Fintype.card (CollisionSlot k)
  let L := r+1
  let behavior (c : Fin s) := cornerBehavior left right (side c)
  have hg (c : Fin s) : 0 < localCornerExponent (behavior c) :=
    (hp.local_corner_parameters_pos (side c) (hactive c)).1
  have hq (c : Fin s) : 0 < localCornerQ (side c) (behavior c) :=
    (hp.local_corner_parameters_pos (side c) (hactive c)).2
  have hkL (c : Fin s) : k c+1 ≤ L := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun c => k c+1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    have hr : r = ∑ c, (k c+1) := by simp [r, CollisionSlot, Fintype.card_sigma]
    dsimp [L]
    omega
  obtain ⟨h0, delta0, v, d, kap, C0, hh0, hd0, hv, hd, hkap, hC0, hlocal⟩ :=
    hp.core_family_local_law grid w hw r
  obtain ⟨M, CM, deltaM, kapM, hCM, hdM, hkapM, hM, hcyl, hMr, hcorner⟩ :=
    hp.factorial_domination_data grid w hw r
  obtain ⟨CK, hCK, hK0, hH0, hKr, hHr, hKt, hHt, hKw⟩ :=
    finite_local_kernel_bounds side behavior hg hq hd
  let C := max CM CK
  have hC : 1 ≤ C := hCM.trans (le_max_left _ _)
  have hCMC : CM ≤ C := le_max_left _ _
  have hCKC : CK ≤ C := le_max_right _ _
  obtain ⟨etaM, heM, heM1, heMb⟩ := factorial_finite_positive_lower_bound
    (fun c => v*kapM/localCornerExponent (behavior c)) (fun c => div_pos (mul_pos hv hkapM) (hg c))
  let eta := min 1 (min kap (min etaM (v/2)))
  have heta : 0 < eta := lt_min zero_lt_one (lt_min hkap (lt_min heM (by positivity)))
  have he1 : eta ≤ 1 := min_le_left _ _
  have hekap : eta ≤ kap := (min_le_right _ _).trans (min_le_left _ _)
  have heM' : eta ≤ etaM := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hev : eta ≤ v/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let delta := min delta0 deltaM
  have hdelta : 0 < delta := lt_min hd0 hdM
  let Q := C^L
  let m : ℝ := (s*L : ℕ)
  let p : ℝ := m^2*Q^2*(2*(2*(2*r : ℕ)+1))
  let Cfinal := (2*C0+(CM+1)*(p+m))*Q^(s+1)
  have hQ : 1 ≤ Q := one_le_pow₀ hC
  have hm : 0 ≤ m := by positivity
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hCF : 0 < Cfinal := by
    have hcoef : 0 < 2*C0+(CM+1)*(p+m) := by positivity
    exact mul_pos hcoef (pow_pos (zero_lt_one.trans_le hQ) _)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ideal_core_eventual_domain h0 hdelta)
  refine ⟨Cfinal, eta, hCF, heta, max 2 N, le_max_left _ _, ?_⟩
  intro n hn P
  obtain ⟨hn2, hhA, hAB, hsepCore, hB⟩ := hN n ((le_max_right _ _).trans hn)
  let A := idealCoreLower n
  let B := idealCoreUpper n
  have hA : 1 ≤ A := idealCoreLower_pos68 n
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  let H := 1+Real.log ((B : ℝ)/A)
  let T := Q*H
  let R := p/(A : ℝ)*T^(s-1)+m*(T/(A : ℝ)^eta)*T^(s-1)
  let K (c : Fin s) (a b : Fin n) := localIdealKernel (side c) (behavior c)
    (cornerDistance (side c) a) (cornerDistance (side c) b)
  let F (c : Fin s) (a b : Fin n) := localEnvelopeKernel (side c) (behavior c) d
    (cornerDistance (side c) a) (cornerDistance (side c) b)
  let bad : CollisionAssignment n A B side k → Prop := coreFamilyBad side behavior k v (2*r)
  have hBt : (B : ℝ) ≤ deltaM*(n : ℝ) :=
    hB.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n))
  have hMt (c : Fin s) (b : CollisionCore n A B (side c)) (a : Fin n) :
      M n a b.val ≤ C/(cornerDistance (side c) b.val : ℝ) := by
    have hb : (cornerDistance (side c) b.val : ℝ) ≤ deltaM*(n : ℝ) :=
      (show (cornerDistance (side c) b.val : ℝ) ≤ B by exact_mod_cast b.property.2).trans hBt
    exact ((hcorner (side c) (hactive c)).1 n b.val hb a).trans
      (div_le_div_of_nonneg_right hCMC (Nat.cast_nonneg _))
  have hMrow (_c : Fin s) (a : Fin n) : (∑ b, M n a b) ≤ C := (hMr n a).trans hCMC
  have hMweighted (c : Fin s) (a : Fin n) :
      (∑ b, (cornerRowRatio (side c) (cornerDistance (side c) a) (cornerDistance (side c) b))^kapM*M n a b) ≤ C :=
    ((hcorner (side c) (hactive c)).2 n a).trans hCMC
  have hKrow (c : Fin s) (a : Fin n) : (∑ b, K c a b) ≤ C := (hKr c n a).trans hCKC
  have hFrow (c : Fin s) (a : Fin n) : (∑ b, F c a b) ≤ C := (hHr c n a).trans hCKC
  have hKtarget (c : Fin s) (b : CollisionCore n A B (side c)) (a : Fin n) :
      K c a b.val ≤ C/(cornerDistance (side c) b.val : ℝ) :=
    (hKt c n a b.val).trans (div_le_div_of_nonneg_right hCKC (Nat.cast_nonneg _))
  have hFtarget (c : Fin s) (b : CollisionCore n A B (side c)) (a : Fin n) :
      F c a b.val ≤ C/(cornerDistance (side c) b.val : ℝ) :=
    (hHt c n a b.val).trans (div_le_div_of_nonneg_right hCKC (Nat.cast_nonneg _))
  have hKweighted (c : Fin s) (a : Fin n) :
      (∑ b, (cornerRowRatio (side c) (cornerDistance (side c) a) (cornerDistance (side c) b))^
        (localCornerExponent (behavior c)/2)*K c a b) ≤ C := (hKw c n a).trans hCKC
  have hbadM : (∑ x : CollisionAssignment n A B side k,
      if bad x then varyingCycleFamilyWeight side k (fun _ => M n) x else 0) ≤ R := by
    have hh := core_family_bad_sum_bound (2*r) hA hAB side behavior k hkL (fun _ => M n)
      (fun _ => hM n) (fun _ => kapM) hC hv (fun _ => hkapM) hg
      (fun c => heM'.trans (heMb c)) hMrow hMweighted hMt
    apply hh.trans_eq
    dsimp [R, p, m, Q, T, H]
    ring
  have hbadK : (∑ x : CollisionAssignment n A B side k,
      if bad x then varyingCycleFamilyWeight side k K x else 0) ≤ R := by
    have he (c : Fin s) : eta ≤ v*(localCornerExponent (behavior c)/2)/localCornerExponent (behavior c) := by
      have heq : v*(localCornerExponent (behavior c)/2)/localCornerExponent (behavior c) = v/2 := by
        field_simp [(hg c).ne']
      rw [heq]
      exact hev
    have hh := core_family_bad_sum_bound (2*r) hA hAB side behavior k hkL K (fun c => hK0 c n)
      (fun c => localCornerExponent (behavior c)/2) hC hv (fun c => div_pos (hg c) (by norm_num)) hg he
      hKrow hKweighted hKtarget
    apply hh.trans_eq
    dsimp [R, p, m, Q, T, H]
    ring
  let eps := C0*((A : ℝ)^(-kap)+((B : ℝ)/(n : ℝ))^kap)
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hEinj (x : CollisionAssignment n A B side k) (hx : ¬ bad x) : Function.Injective (collisionLabel x) :=
    core_family_injective_of_separated (2*r) x (fun h => hx (Or.inl h))
  have hl (x : CollisionAssignment n A B side k) (hx : ¬ bad x) :
      |coreFamilyRankProbability (w n) x-varyingCycleFamilyWeight side k K x| ≤
        eps*varyingCycleFamilyWeight side k F x := by
    exact hlocal s n A B side k le_rfl hactive hA hhA
      (hB.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))) x (hEinj x hx)
      (fun p q hpq => lt_of_not_ge (fun hh => hx (Or.inl ⟨p, q, hpq, hh⟩)))
      (fun p h => hx (Or.inr ⟨p, h⟩))
  have hh := core_family_comparison_of_bounds side behavior k P (w n) (M n) (hM n) (fun c => hK0 c n)
    (varyingCycleFamilyWeight side k F) (varying_cycle_family_nonneg side k F (fun c => hH0 c n))
    bad (zero_le_one.trans hCM) heps (hcyl n) le_rfl hEinj hl hbadM hbadK
  have htrace := varying_cycle_family_sum_bound hA hAB side k hkL F (fun c => hH0 c n) hC hFrow hFtarget
  have hinputs := factorial_core_error_inputs (show 0 < n by omega) hA hAB (ideal_core_upper_le_div n)
  have hnumer := factorial_error_algebra hA1 hinputs.1 hinputs.2.1 hkap he1 hekap hC0.le
    (zero_le_one.trans hCM) hp0 hm hQ hinputs.2.2.1 hinputs.2.2.2 s
  calc
    _ ≤ eps*(∑ x : CollisionAssignment n A B side k, varyingCycleFamilyWeight side k F x)+CM*R+R := hh
    _ ≤ eps*T^s+CM*R+R := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left htrace heps) le_rfl) le_rfl
    _ = C0*((A : ℝ)^(-kap)+((B : ℝ)/(n : ℝ))^kap)*(Q*H)^s +
        (CM+1)*(p/(A : ℝ)*(Q*H)^(s-1)+m*((Q*H)/(A : ℝ)^eta)*(Q*H)^(s-1)) := by
      dsimp [eps, R, T]
      ring
    _ ≤ (2*C0+(CM+1)*(p+m))*Q^(s+1)*(1+Real.log (n : ℝ))^(s+1)*(A : ℝ)^(-eta) := hnumer
    _ = _ := by rfl

end Luce.Section6
