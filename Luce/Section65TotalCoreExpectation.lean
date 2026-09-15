import Luce.Section65TotalCoreComparison
import Luce.Section65TotalCoreCutoffs
import Luce.Section65RootSums
import Luce.Section65CountApproximation

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Luce.Section6

theorem race_integral_add65 {n : ℕ} (w : Weights n) (F G : Equiv.Perm (Fin n) → ℝ) :
    (∫ z, F (raceRankPermutation z)+G (raceRankPermutation z) ∂exponentialRace w) =
      (∫ z, F (raceRankPermutation z) ∂exponentialRace w)+
      (∫ z, G (raceRankPermutation z) ∂exponentialRace w) :=
  integral_add (integrable_race_permutation_statistic w F) (integrable_race_permutation_statistic w G)

theorem race_integral_sum65 {n : ℕ} {ι : Type*} [Fintype ι] (w : Weights n)
    (F : ι → Equiv.Perm (Fin n) → ℝ) :
    (∫ z, ∑ i, F i (raceRankPermutation z) ∂exponentialRace w) =
      ∑ i, ∫ z, F i (raceRankPermutation z) ∂exponentialRace w :=
  integral_finsetSum _ (fun i _ => integrable_race_permutation_statistic w (F i))

theorem totalCore_error_bound65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ clocks, |(Section5.cycleCount (raceRankPermutation clocks) k : ℝ)-
        totalCoreCount65 (raceRankPermutation clocks) left right k| ∂exponentialRace (w n)) ≤
          C*(1+Real.log (idealCoreLower n : ℝ)) := by
  classical
  obtain ⟨C,d,q,hC,hd,hd1,hq,hest⟩ := lemma67_active f left right hp (k+1)
  obtain ⟨D,hD,hoff⟩ := lemma67_regular f left right hp (k+1) d hd hd1
  refine ⟨D+(Fintype.card (ActiveCorner65 left right) : ℝ)*(4*C),by positivity,?_⟩
  filter_upwards [ideal_core_eventual_domain 1 hd] with n hn
  let H := 1+Real.log (idealCoreLower n : ℝ)
  have hH : 1 ≤ H := by have := Real.log_natCast_nonneg (idealCoreLower n); dsimp [H]; linarith
  have hA1 : (1 : ℝ) ≤ idealCoreLower n := by exact_mod_cast hn.2.1
  have hAB : (idealCoreLower n : ℝ) ≤ idealCoreUpper n := by exact_mod_cast hn.2.2.1
  have hB1 : (1 : ℝ) ≤ idealCoreUpper n := hA1.trans hAB
  have hBn : (idealCoreUpper n : ℝ) ≤ n := by exact_mod_cast ideal_core_upper_le_population n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hside (s : ActiveCorner65 left right) :
      (∫ clocks, (selectedRootCycleCount (raceRankPermutation clocks) k (lowRootLabels65 s.val n d) : ℝ)
        ∂exponentialRace (w n))+
      (∫ clocks, (selectedRootCycleCount (raceRankPermutation clocks) k (highRootLabels65 s.val n d) : ℝ)
        ∂exponentialRace (w n))+
      (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) s.val k (idealCoreLower n) (idealCoreUpper n) : ℝ)
        ∂exponentialRace (w n)) ≤ 4*C*H := by
    have he := hest k (by omega) s.val s.property grid w hs
    have hlo := selectedRootCycleCount_harmonic65 (w n) s.val k (lowRootLabels65 s.val n d)
      hC.le (show (1 : ℝ) ≤ 1 by rfl) hA1
      (fun v hv => ⟨by exact_mod_cast (cornerDistance_pos67 s.val v),
        by exact_mod_cast (Finset.mem_filter.mp hv).2.1.le⟩)
      (fun v hv => he.1 n v (Finset.mem_filter.mp hv).2.2)
    simp only [div_one] at hlo
    have hhi := selectedRootCycleCount_harmonic65 (w n) s.val k (highRootLabels65 s.val n d)
      hC.le hB1 hBn
      (fun v hv => ⟨by exact_mod_cast (Finset.mem_filter.mp hv).2.1.le,
        by exact_mod_cast cornerDistance_le_population65 s.val v⟩)
      (fun v hv => he.1 n v (Finset.mem_filter.mp hv).2.2)
    have hlog := log_population_core_upper65 (show 1 ≤ n by omega) hn.2.2.1
    have hhi' : (∫ clocks, (selectedRootCycleCount (raceRankPermutation clocks) k (highRootLabels65 s.val n d) : ℝ)
        ∂exponentialRace (w n)) ≤ 2*C*H := by
      have hmult := mul_le_mul_of_nonneg_left (show 1+Real.log ((n : ℝ)/(idealCoreUpper n : ℝ)) ≤ 2*H by
        dsimp [H] at *; linarith) hC.le
      exact hhi.trans (hmult.trans_eq (by ring))
    have hdis := he.2.1 n (idealCoreLower n) (idealCoreUpper n) hA1 hAB
      ((div_le_iff₀ hn0).mpr hn.2.2.2.2)
    have hCH : C ≤ C*H := le_mul_of_one_le_right hC.le hH
    dsimp [H] at *
    linarith
  have hm := integral_mono (integrable_race_permutation_statistic (w n) (fun R =>
      |(Section5.cycleCount R k : ℝ)-totalCoreCount65 R left right k|))
    (integrable_race_permutation_statistic (w n) (fun R =>
      (selectedRootCycleCount R k (offActiveLabels left right n d) : ℝ)+
        ∑ s : ActiveCorner65 left right,
          ((selectedRootCycleCount R k (lowRootLabels65 s.val n d) : ℝ)+
           (selectedRootCycleCount R k (highRootLabels65 s.val n d) : ℝ)+
           (intervalDiscardedCycleCount R s.val k (idealCoreLower n) (idealCoreUpper n) : ℝ))))
    (fun clocks => totalCoreCount_error65 (raceRankPermutation clocks) left right k d hn.2.2.2.1)
  rw [race_integral_add65 (w n)
    (fun R => (selectedRootCycleCount R k (offActiveLabels left right n d) : ℝ))
    (fun R => ∑ s : ActiveCorner65 left right,
      ((selectedRootCycleCount R k (lowRootLabels65 s.val n d) : ℝ)+
       (selectedRootCycleCount R k (highRootLabels65 s.val n d) : ℝ)+
       (intervalDiscardedCycleCount R s.val k (idealCoreLower n) (idealCoreUpper n) : ℝ))),
    race_integral_sum65 (w n) (fun (s : ActiveCorner65 left right) R =>
      (selectedRootCycleCount R k (lowRootLabels65 s.val n d) : ℝ)+
      (selectedRootCycleCount R k (highRootLabels65 s.val n d) : ℝ)+
      (intervalDiscardedCycleCount R s.val k (idealCoreLower n) (idealCoreUpper n) : ℝ))] at hm
  have hadd (s : ActiveCorner65 left right) :
      (∫ clocks,
        (selectedRootCycleCount (raceRankPermutation clocks) k (lowRootLabels65 s.val n d) : ℝ)+
        (selectedRootCycleCount (raceRankPermutation clocks) k (highRootLabels65 s.val n d) : ℝ)+
        (intervalDiscardedCycleCount (raceRankPermutation clocks) s.val k (idealCoreLower n) (idealCoreUpper n) : ℝ)
          ∂exponentialRace (w n)) =
      (∫ clocks, (selectedRootCycleCount (raceRankPermutation clocks) k (lowRootLabels65 s.val n d) : ℝ)
        ∂exponentialRace (w n))+
      (∫ clocks, (selectedRootCycleCount (raceRankPermutation clocks) k (highRootLabels65 s.val n d) : ℝ)
        ∂exponentialRace (w n))+
      (∫ clocks, (intervalDiscardedCycleCount (raceRankPermutation clocks) s.val k (idealCoreLower n) (idealCoreUpper n) : ℝ)
        ∂exponentialRace (w n)) := by
    rw [race_integral_add65 (w n)
      (fun R => (selectedRootCycleCount R k (lowRootLabels65 s.val n d) : ℝ)+
        (selectedRootCycleCount R k (highRootLabels65 s.val n d) : ℝ))
      (fun R => (intervalDiscardedCycleCount R s.val k (idealCoreLower n) (idealCoreUpper n) : ℝ)),
      race_integral_add65 (w n)
        (fun R => (selectedRootCycleCount R k (lowRootLabels65 s.val n d) : ℝ))
        (fun R => (selectedRootCycleCount R k (highRootLabels65 s.val n d) : ℝ))]
  simp only [hadd] at hm
  have hoffn := hoff grid w hs n k (by omega)
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (ActiveCorner65 left right))) => hside s)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hDH : D ≤ D*H := le_mul_of_one_le_right hD.le hH
  dsimp [H] at *
  nlinarith only [hm,hoffn,hsum,hDH]

theorem totalCount_approx65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (k : ℕ) : CountApprox65 w (fun _ R => (Section5.cycleCount R k : ℝ))
      (fun _ R => totalCoreCount65 R left right k) := by
  obtain ⟨C,hC,h⟩ := totalCore_error_bound65 f left right hp grid w hs k
  exact countApprox65_of_bound w _ _ h

end Luce.Section6
