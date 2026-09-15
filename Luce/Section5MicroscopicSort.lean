import Luce.Section5MarkedSort
import Luce.Section5MarkedCoefficientLimit
import Luce.Section5CyclicAnalytic

/-!
# Removal of rank-order conventions from the microscopic estimate

Sorting permutes the marked pairs together. The event and every product
are preserved exactly, with no factorial. A fixed positive macroscopic
separation makes the deleted gaps distinct for all sufficiently large n;
the fixed bulk margin simultaneously excludes the terminal gap.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Function Filter Set
open scoped BigOperators Topology

namespace Luce
attribute [local instance] Classical.propDecidable

lemma real_coe_nat_dist (a b : ℕ) : (Nat.dist a b : ℝ) = |(a : ℝ) - b| := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

/-- An auxiliary reduction from a proved sorted finite-gap estimate.
The main microscopic theorem must discharge `hsorted`; it is not an
assumed spacing law or a claimed completed asymptotic. -/
theorem bounded_marked_asymptotic_of_sorted
    (w : WeightArray) (f : ℝ → ℝ) (r : ℕ) {α : ℝ} (hα : α < 1) (M : ℝ)
    (hsorted : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ u j : Fin r → Fin n, Injective u → StrictMono j →
        ∀ q : Fin r ↪ Fin (Finset.univ \ Finset.univ.image u).card,
          StrictMono (fun a => (q a).val) →
          (∀ a, (q a).val + a.val = (j a).val) →
          (∀ a, (w n).rate (u a) ≤ M) →
          (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
          |(n : ℝ) ^ r * (exponentialRace (w n)).real {old | MarkedRankCylinder u j old} -
            ∏ a, profileGapCoefficient f ((w n).rate (u a))
              (((j a).val + (1 : ℝ)) / n)| < ε) :
    ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin r ↪ Fin n,
        (∀ a, (w n).rate (i a) ≤ M) →
        (∀ a, (j a).val + (1 : ℝ) ≤ α * n) →
        (∀ a b, a ≠ b → ζ * n ≤ |((j a).val : ℝ) - (j b).val|) →
        |(n : ℝ) ^ r * (exponentialRace (w n)).real
            {old | ∀ a, raceRank old (i a) = (j a).val + 1} -
          ∏ a, finiteCyclicDensity (w n) f (i a) (j a)| < ε := by
  intro ζ hζ ε hε
  have hmargin : ∀ᶠ n : ℕ in atTop, (r : ℝ) ≤ (1 - α) * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop ((r : ℝ) / (1 - α)))] with n hn
    have h := (div_le_iff₀ (sub_pos.mpr hα)).mp hn
    linarith
  have hsepmargin : ∀ᶠ n : ℕ in atTop, (r : ℝ) ≤ ζ * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop ((r : ℝ) / ζ))] with n hn
    have h := (div_le_iff₀ hζ).mp hn
    linarith
  filter_upwards [hsorted ε hε, hmargin, hsepmargin] with n hn hmar hsepN
  intro i j hi hj hsep
  let e := Tuple.sort (j : Fin r → Fin n)
  let u' : Fin r → Fin n := i ∘ e
  let j' : Fin r → Fin n := j ∘ e
  have hsepNat : ∀ a b, a ≠ b → r ≤ Nat.dist (j a).val (j b).val := by
    intro a b hab
    have h := hsepN.trans (hsep a b hab)
    rw [← real_coe_nat_dist] at h
    exact_mod_cast h
  have hstrict := sortedMarkedGapIndex_strictMono (j : Fin r → Fin n) j.injective hsepNat
  have hbulk : ∀ a, (j a).val + r < n := by
    intro a
    have ha := hj a
    have hr : ((j a).val : ℝ) + r < n := by linarith
    exact_mod_cast hr
  have hcard : (Finset.univ \ Finset.univ.image u').card =
      (Finset.univ \ Finset.univ.image (i : Fin r → Fin n)).card := by
    rw [show u' = (i : Fin r → Fin n) ∘ e from rfl, markedImage_comp_perm]
  let q : Fin r ↪ Fin (Finset.univ \ Finset.univ.image u').card :=
    ⟨fun a => ⟨sortedMarkedGapIndex (j : Fin r → Fin n) a, by
      rw [hcard]
      exact sortedMarkedGapIndex_lt_complement (i : Fin r → Fin n) j i.injective hbulk a⟩,
      fun a b hab => hstrict.injective (congrArg Fin.val hab)⟩
  have hq : StrictMono (fun a => (q a).val) := hstrict
  have hindex : ∀ a, (q a).val + a.val = (j' a).val :=
    sortedMarkedGapIndex_add (j : Fin r → Fin n) j.injective
  have h := hn u' j' (i.injective.comp e.injective)
    (strictMono_sorted_markedRanks (j : Fin r → Fin n) j.injective)
    q hq hindex (fun a => hi (e a)) (fun a => hj (e a))
  have hevent : {old | MarkedRankCylinder u' j' old} =
      {old | ∀ a, raceRank old (i a) = (j a).val + 1} := by
    ext old
    exact markedRankCylinder_comp_perm (i : Fin r → Fin n) j e old
  have hprod : (∏ a, profileGapCoefficient f ((w n).rate (u' a))
      (((j' a).val + (1 : ℝ)) / n)) = ∏ a, finiteCyclicDensity (w n) f (i a) (j a) := by
    simpa only [u', j', Function.comp_apply, finiteCyclicDensity, profileGapCoefficient] using
      Equiv.prod_comp e (fun a => finiteCyclicDensity (w n) f (i a) (j a))
  rw [hevent, hprod] at h
  exact h

end Luce
