import Luce.Section6LogExcursionProbability
import Luce.Section6FilteredCycleCount

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace Luce.Section6

theorem logarithmic_excursion_expectation_of_root_bound {n : ℕ} (w : Weights n)
    (side : Corner) (k : ℕ) {C delta q : ℝ} (hC : 0 < C)
    (hprob : ∀ (v : Fin n) (R : ℝ), 1 ≤ R →
      (cornerDistance side v : ℝ)/(n : ℝ) ≤ delta →
      (exponentialRace w).real (rootLogExcursionEvent side k v R) ≤
        C/(cornerDistance side v : ℝ)*R^(-q))
    {A B R : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (hB : B/(n : ℝ) ≤ delta)
    (hR : 1 ≤ R) :
    (∫ clocks, (logarithmicExcursionCount (raceRankPermutation clocks) side k A B R : ℝ)
      ∂exponentialRace w) ≤ C*(1+Real.log (B/A))*R^(-q) := by
  classical
  let P : Fin n → Cycle (Fin n) → Prop := fun v orb =>
    A ≤ (cornerDistance side v : ℝ) ∧ (cornerDistance side v : ℝ) ≤ B ∧
    ∃ z ∈ orb.toFinset,
      Real.log R ≤ |Real.log (cornerDistance side z)-Real.log (cornerDistance side v)|
  let E := fun v : Fin n => {clocks : Fin n → ℝ |
    v ∈ Section5.maximumCycleRoots (raceRankPermutation clocks) k ∧
    P v (periodicOrbit (raceRankPermutation clocks : Fin n → Fin n) v)}
  let S := Finset.univ.filter fun v : Fin n =>
    A ≤ (cornerDistance side v : ℝ) ∧ (cornerDistance side v : ℝ) ≤ B
  have he : (∫ clocks, (logarithmicExcursionCount (raceRankPermutation clocks) side k A B R : ℝ)
      ∂exponentialRace w) = ∑ v, (exponentialRace w).real (E v) := by
    convert filtered_cycle_expectation_eq_probability_sum w k P using 1
    apply integral_congr_ae
    filter_upwards [] with clocks
    apply congrArg (fun s : Finset ↥(Section5.cycleOrbits (raceRankPermutation clocks) k) => (s.card : ℝ))
    ext c
    simp [logarithmicExcursionCount, P]
  have hpoint (v : Fin n) : (exponentialRace w).real (E v) ≤
      if v ∈ S then C/(cornerDistance side v : ℝ)*R^(-q) else 0 := by
    by_cases hv : v ∈ S
    · rw [if_pos hv]
      have hvd : (cornerDistance side v : ℝ)/(n : ℝ) ≤ delta :=
        (div_le_div_of_nonneg_right (Finset.mem_filter.mp hv).2.2 (Nat.cast_nonneg _)).trans hB
      apply le_trans _ (hprob v R hR hvd)
      apply measureReal_mono _ (measure_ne_top _ _)
      intro clocks hc
      exact ⟨hc.1, hc.2.2.2⟩
    · rw [if_neg hv]
      have hempty : E v = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro clocks hc
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.2.1, hc.2.2.1⟩)
      simp [hempty]
  have hsum : (∑ v ∈ S, 1/(cornerDistance side v : ℝ)) ≤ 1+Real.log (B/A) := by
    have himage : (∑ m ∈ S.image (cornerDistance side), 1/(m : ℝ)) =
        ∑ v ∈ S, 1/(cornerDistance side v : ℝ) :=
      Finset.sum_image (fun i _ j _ hij => cornerDistance_injective67 side hij)
    rw [← himage]
    apply harmonic_real_subset67 _ hA hAB
    intro m hm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
    exact (Finset.mem_filter.mp hv).2
  rw [he]
  calc
    _ ≤ ∑ v : Fin n, if v ∈ S then C/(cornerDistance side v : ℝ)*R^(-q) else 0 :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ = C*R^(-q) * ∑ v ∈ S, 1/(cornerDistance side v : ℝ) := by
      rw [Finset.mul_sum]
      simp only [← Finset.sum_filter]
      apply Finset.sum_congr (by ext v; simp)
      intro v hv
      ring
    _ ≤ C*R^(-q)*(1+Real.log (B/A)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

theorem PowerProfile.active_log_expectation {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (k : ℕ) (side : Corner) :
    ∃ C delta q : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧ 0 < q ∧
    ((cornerBehavior left right side).active →
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (A B R : ℝ), 1 ≤ A → A ≤ B → B/(n : ℝ) ≤ delta → 1 ≤ R →
      (∫ clocks, (logarithmicExcursionCount (raceRankPermutation clocks) side k A B R : ℝ)
        ∂exponentialRace (w n)) ≤ C*(1+Real.log (B/A))*R^(-q)) := by
  have hconvert (side : Corner)
      (h : ∃ C delta q : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧ 0 < q ∧
        ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
        ∀ (n : ℕ) (v : Fin n) (R : ℝ), 1 ≤ R →
          (cornerDistance side v : ℝ)/(n : ℝ) ≤ delta →
          (exponentialRace (w n)).real (rootLogExcursionEvent side k v R) ≤
            C/(cornerDistance side v : ℝ)*R^(-q)) :
      ∃ C delta q : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧ 0 < q ∧
      ((cornerBehavior left right side).active →
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (A B R : ℝ), 1 ≤ A → A ≤ B → B/(n : ℝ) ≤ delta → 1 ≤ R →
        (∫ clocks, (logarithmicExcursionCount (raceRankPermutation clocks) side k A B R : ℝ)
          ∂exponentialRace (w n)) ≤ C*(1+Real.log (B/A))*R^(-q)) := by
    obtain ⟨C, d, q, hC, hd, hd1, hq, hb⟩ := h
    refine ⟨C, d, q, hC, hd, hd1, hq, ?_⟩
    intro _ grid w hw n A B R hA hAB hB hR
    exact logarithmic_excursion_expectation_of_root_bound (w n) side k hC
      (hb grid w hw n) hA hAB hB hR
  cases side with
  | left =>
    cases left with
    | finite c => exact ⟨1, 1/2, 1, by norm_num, by norm_num, by norm_num,
        by norm_num, by simp [cornerBehavior, EndpointBehavior.active]⟩
    | power c alpha eta => exact hconvert .left (hp.left_root_log_probability k)
  | right =>
    cases right with
    | finite c => exact ⟨1, 1/2, 1, by norm_num, by norm_num, by norm_num,
        by norm_num, by simp [cornerBehavior, EndpointBehavior.active]⟩
    | power c beta eta => exact hconvert .right (hp.right_root_log_probability k)

end Luce.Section6
