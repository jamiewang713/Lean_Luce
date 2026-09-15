import Luce.Section65CoreNormalizedMoments
import Luce.Section65MeanAsymptotic

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Luce.Section6

def FiniteCategoriesDisjoint65 {ι : Type*} (c : ι → CoreCycleCategory) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ i j : ι, i ≠ j → (c i).side = (c j).side →
    (c i).lengthIndex = (c j).lengthIndex → ∀ m : ℕ,
      ¬ ((c i).rootWindow.Allows n m ∧ (c j).rootWindow.Allows n m)

theorem core_normalized_finite_moments65 {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (left right : EndpointBehavior) (hp : PowerProfile f left right)
    (grid : SamplingGrid) (w : WeightArray) (hs : SampledRates grid w f)
    (c : ι → CoreCycleCategory)
    (ha : ∀ i, (cornerBehavior left right (c i).side).active)
    (hd : FiniteCategoriesDisjoint65 c)
    (β : ι → ℝ) (hβ : ∀ i, 0 < β i)
    (hm : ∀ i, MeanApprox65 (fun n => coreCategoryIdealMean left right n (c i)) (β i))
    (r : ι → ℕ) :
    Tendsto (fun n => ∫ clocks, ∏ i : ι,
      (normalizedCoreCategory65 left right (raceRankPermutation clocks) (c i))^(r i)
        ∂exponentialRace (w n)) atTop (𝓝 (∏ i, gaussianMoment65 1 (r i))) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hd' : CoreCategoriesDisjoint (fun i => c (e i)) := by
    intro n hn i j hij hside hlen m
    exact hd n hn (e i) (e j) (e.injective.ne hij) hside hlen m
  have h := core_normalized_mixed_moments65 f left right hp grid w hs (Fintype.card ι)
    (fun i => c (e i)) (fun i => ha (e i)) hd'
    (fun i => (hm (e i)).growth) (fun i => (hm (e i)).diverges (hβ (e i))) (fun i => r (e i))
  have he (n : ℕ) (clocks : Fin n → ℝ) :
      (∏ i : Fin (Fintype.card ι),
        (normalizedCoreCategory65 left right (raceRankPermutation clocks) (c (e i)))^(r (e i))) =
      ∏ i : ι, (normalizedCoreCategory65 left right (raceRankPermutation clocks) (c i))^(r i) :=
    e.prod_comp (fun i => (normalizedCoreCategory65 left right (raceRankPermutation clocks) (c i))^(r i))
  have ht : (∏ i : Fin (Fintype.card ι), gaussianMoment65 1 (r (e i))) =
      ∏ i : ι, gaussianMoment65 1 (r i) := e.prod_comp (fun i => gaussianMoment65 1 (r i))
  simpa only [he,ht] using h

end Luce.Section6
