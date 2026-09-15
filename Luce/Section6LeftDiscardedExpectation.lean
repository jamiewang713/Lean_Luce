import Luce.Section6DiscardedCountDefinitions
import Luce.Section6FilteredCycleCount
import Luce.Section6ExcursionDepthSums

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace Luce.Section6

/-- The complete left discarded-cycle expectation bound for integer
cutoffs, with all probability and depth-sum premises discharged. -/
theorem PowerProfile.left_discarded_expectation_nat {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (k : ℕ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n A B : ℕ), 1 ≤ A → A ≤ B → (B : ℝ)/(n : ℝ) ≤ delta →
      (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) .left k A B : ℝ)
        ∂exponentialRace (w n)) ≤ C := by
  classical
  obtain ⟨K, q, delta, hK, hq, hd, hd1, hprob⟩ := hp.left_excursion_cycle_probability k
  refine ⟨K*(1+1/q), delta, by positivity, hd, hd1, ?_⟩
  intro grid w hw n A B hA hAB hB
  let d : Fin n → ℕ := fun v => v.val+1
  let P : Fin n → Cycle (Fin n) → Prop := fun v orb =>
    (A : ℝ) ≤ ((v.val : ℝ)+1) ∧ ((v.val : ℝ)+1) ≤ B ∧
    ∃ z ∈ orb.toFinset, ¬ ((A : ℝ) ≤ (z.val : ℝ)+1 ∧ (z.val : ℝ)+1 ≤ B)
  let E := fun v : Fin n => {clocks : Fin n → ℝ |
    v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k ∧
    P v (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v)}
  let S := Finset.univ.filter (fun v : Fin n => A ≤ d v ∧ d v ≤ B)
  let g : ℕ → ℝ := fun m => (1/(m : ℝ))*((A : ℝ)/(m : ℝ))^q
  have he : (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) .left k A B : ℝ)
      ∂exponentialRace (w n)) = ∑ v, (exponentialRace (w n)).real (E v) := by
    convert filtered_cycle_expectation_eq_probability_sum (w n) k P using 1
    apply integral_congr_ae
    filter_upwards [] with clocks
    apply congrArg (fun s : Finset ↥(Section5.cycleOrbits (raceRankPermutation clocks) k) => (s.card : ℝ))
    ext c
    simp [cornerDistance, P, Nat.cast_add, Nat.cast_one]
  have hpoint (v : Fin n) : (exponentialRace (w n)).real (E v) ≤
      if v ∈ S then K*g (d v) else 0 := by
    by_cases hv : v ∈ S
    · rw [if_pos hv]
      obtain ⟨hav, hvb⟩ := (Finset.mem_filter.mp hv).2
      have havR : (A : ℝ) ≤ (v.val : ℝ)+1 := by exact_mod_cast hav
      have hvbR : (v.val : ℝ)+1 ≤ B := by exact_mod_cast hvb
      have hAr : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
      have hvd : ((v.val : ℝ)+1)/(n : ℝ) ≤ delta :=
        (div_le_div_of_nonneg_right hvbR (Nat.cast_nonneg _)).trans hB
      have hb := hprob grid w hw n v A hAr havR hvd
      have hcast : K*g (d v) =
          K/((v.val : ℝ)+1)*((1/((v.val : ℝ)+1)^q)/(1/(A : ℝ)^q)) := by
        dsimp [g, d]
        rw [Nat.cast_add, Nat.cast_one, Real.div_rpow (Nat.cast_nonneg _) (by positivity)]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hAr q),
          ne_of_gt (Real.rpow_pos_of_pos (show (0 : ℝ) < (v.val : ℝ)+1 by positivity) q)]
        <;> ring
      rw [hcast]
      apply le_trans _ hb
      apply measureReal_mono _ (measure_ne_top _ _)
      intro clocks hc
      exact ⟨((Section5.mem_maximumCycleRoots_iff _ k v).mp hc.1).1,
        (maximum_root_left_escape_iff _ k v hc.1 hvbR).mp hc.2.2.2⟩
    · rw [if_neg hv]
      have hempty : E v = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro clocks hc
        apply hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          by exact_mod_cast hc.2.1, by exact_mod_cast hc.2.2.1⟩
      simp [hempty]
  have hinj : Injective d := by
    intro i j hij
    exact Fin.ext (Nat.add_right_cancel hij)
  have himage : (∑ m ∈ S.image d, g m) = ∑ v ∈ S, g (d v) :=
    Finset.sum_image (fun i _ j _ hij => hinj hij)
  have hsum : (∑ v ∈ S, g (d v)) ≤ 1+1/q := by
    rw [← himage]
    apply le_trans _ (left_excursion_kernel_sum hq hA hAB)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hv).2
    · intro m hm hnot
      dsimp [g]
      positivity
  rw [he]
  calc
    _ ≤ ∑ v : Fin n, if v ∈ S then K*g (d v) else 0 :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ = K * ∑ v ∈ S, g (d v) := by rw [Finset.mul_sum]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hK.le

end Luce.Section6
