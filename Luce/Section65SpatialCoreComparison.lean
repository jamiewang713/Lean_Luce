import Luce.Section65CoreCountComparison
import Luce.Section65LogWindows
import Luce.Section6Lemma67
import Luce.Section6FactorialCoreCutoffs
import Luce.Section5FiniteStatistic

noncomputable section
open MeasureTheory Filter
namespace Luce.Section6
attribute [local instance] Classical.propDecidable

def spatialCoreCategory65 (side : Corner) (k : ℕ) (a b : ℝ) : CoreCycleCategory :=
  ⟨side,k,.interval (fun n => (n : ℝ)^a) (fun n => (n : ℝ)^b)⟩

theorem spatial_windowCount65 {n : ℕ} (hn : 2 ≤ n) (R : Equiv.Perm (Fin n))
    (side : Corner) (k : ℕ) (a b : ℝ) :
    (Finset.univ.filter (fun d : ↥(Section5.cycleOrbits R k) =>
      (spatialCoreCategory65 side k a b).rootWindow.Allows n
        (cornerDistance side (Section5.cycleMaximum R k d)))).card =
      spatialCycleCount R side k a b := by
  unfold spatialCycleCount
  apply congrArg Finset.card
  ext d
  constructor
  · intro hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (logLocation_window_iff65 hn side (Section5.cycleMaximum R k d) a b).mpr (Finset.mem_filter.mp hd).2⟩
  · intro hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (logLocation_window_iff65 hn side (Section5.cycleMaximum R k d) a b).mp (Finset.mem_filter.mp hd).2⟩

theorem spatialCore_count_le65 {n : ℕ} (hn : 2 ≤ n) (R : Equiv.Perm (Fin n))
    (side : Corner) (k : ℕ) (a b : ℝ) :
    coreCategoryCount R (spatialCoreCategory65 side k a b) ≤ spatialCycleCount R side k a b := by
  have h := coreCount_le_windowCount65 R (spatialCoreCategory65 side k a b)
  apply h.trans_eq
  convert spatial_windowCount65 hn R side k a b using 1 <;> congr 1 <;> ext d <;> simp

theorem spatialCore_error_bound65 (f : ℝ → ℝ) (left right : EndpointBehavior)
    (hp : PowerProfile f left right) (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (side : Corner) (ha : (cornerBehavior left right side).active) (k : ℕ) {a b : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ clocks, |(spatialCycleCount (raceRankPermutation clocks) side k a b : ℝ)-
        (coreCategoryCount (raceRankPermutation clocks) (spatialCoreCategory65 side k a b) : ℝ)|
          ∂exponentialRace (w n)) ≤ C := by
  obtain ⟨C,d,q,hC,hd,hd1,hq,hest⟩ := lemma67_active f left right hp (k+1)
  have hdisc := (hest k (by omega) side ha grid w hs).2.1
  refine ⟨C,hC,?_⟩
  filter_upwards [ideal_core_eventual_domain 1 hd,power_window_inside_core65 ha0 hab hb1]
    with n hn hw
  apply le_trans _ (hdisc n (idealCoreLower n) (idealCoreUpper n)
    (by exact_mod_cast hn.2.1) (by exact_mod_cast hn.2.2.1)
    ((div_le_iff₀ (by exact_mod_cast (show 0 < n by omega))).mpr hn.2.2.2.2))
  apply integral_mono
    (integrable_race_permutation_statistic (w n) (fun R =>
      |(spatialCycleCount R side k a b : ℝ)-(coreCategoryCount R (spatialCoreCategory65 side k a b) : ℝ)|))
    (integrable_race_permutation_statistic (w n) (fun R =>
      (intervalDiscardedCycleCount R side k (idealCoreLower n) (idealCoreUpper n) : ℝ)))
  intro clocks
  dsimp only
  have hle : (coreCategoryCount (raceRankPermutation clocks) (spatialCoreCategory65 side k a b) : ℝ) ≤
      (spatialCycleCount (raceRankPermutation clocks) side k a b : ℝ) := by
    exact_mod_cast (spatialCore_count_le65 hn.1 (raceRankPermutation clocks) side k a b)
  rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  have h := windowCount_sub_coreCount_le_discarded65 (raceRankPermutation clocks)
    (spatialCoreCategory65 side k a b) (fun v hv => hw _ hv.1 hv.2)
  have he : ((Finset.univ.filter (fun d : ↥(Section5.cycleOrbits (raceRankPermutation clocks)
      (spatialCoreCategory65 side k a b).lengthIndex) =>
      (spatialCoreCategory65 side k a b).rootWindow.Allows n
        (cornerDistance (spatialCoreCategory65 side k a b).side
          (Section5.cycleMaximum (raceRankPermutation clocks) (spatialCoreCategory65 side k a b).lengthIndex d)))).card) =
      spatialCycleCount (raceRankPermutation clocks) side k a b := by
    convert spatial_windowCount65 hn.1 (raceRankPermutation clocks) side k a b using 1 <;>
      congr 1 <;> ext d <;> simp
  rwa [he] at h

end Luce.Section6
