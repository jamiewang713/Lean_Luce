import Luce.Section6PopulationSeparation
import Luce.Section6QuantileMoments

noncomputable section
namespace Luce.Section6

/-- Integrating the actual derivative lower bound gives separation on both
sides of the center. This helper's window premise is discharged below. -/
theorem populationG_mean_separation {n : ℕ} (hn : 0 < n) (w : Weights n)
    {a m t u : ℝ} (ht : 0 < t) (hu : 0 < u) (hu' : u ≤ 1/2)
    (hlower : ∀ s : ℝ, t/4 ≤ s → s ≤ 4*t →
      a*m/t ≤ (n : ℝ)*populationD w 1 s) :
    a*u*m ≤ (n : ℝ)*(populationG w ((1+u)*t)-populationG w t) ∧
    a*u*m ≤ (n : ℝ)*(populationG w t-populationG w ((1-u)*t)) := by
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hut : 0 ≤ u*t := (mul_pos hu ht).le
  have hplus : t ≤ (1+u)*t := by nlinarith
  have hminus : (1-u)*t ≤ t := by nlinarith
  have hp := (populationG_separation hn w hplus).1
  have hm := (populationG_separation hn w hminus).1
  have hlp := hlower ((1+u)*t) (by nlinarith) (by nlinarith)
  have hlc := hlower t (by linarith) (by linarith)
  have heq : (a*m/t)*(u*t) = a*u*m := by field_simp
  constructor
  · have h1 := mul_le_mul_of_nonneg_right hlp hut
    have h2 := mul_le_mul_of_nonneg_left hp hnR
    rw [heq] at h1
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_right hlc hut
    have h2 := mul_le_mul_of_nonneg_left hm hnR
    rw [heq] at h1
    nlinarith

theorem populationH_mean_separation {n : ℕ} (hn : 0 < n) (w : Weights n)
    {a m t u : ℝ} (ht : 0 < t) (hu : 0 < u) (hu' : u ≤ 1/2)
    (hlower : ∀ s : ℝ, t/4 ≤ s → s ≤ 4*t →
      a*m/t ≤ (n : ℝ)*populationD w 1 s) :
    a*u*m ≤ (n : ℝ)*(populationH w t-populationH w ((1+u)*t)) ∧
    a*u*m ≤ (n : ℝ)*(populationH w ((1-u)*t)-populationH w t) := by
  have h := populationG_mean_separation hn w ht hu hu' hlower
  simp only [populationG_eq_one_sub_H hn w] at h
  constructor <;> nlinarith [h.1, h.2]

theorem PowerProfile.right_quantile_mean_separation {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ a delta M : ℝ, 0 < a ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := rightQuantileTime (w n) m
      ∀ u : ℝ, 0 < u → u ≤ 1/2 →
        a*u*(m : ℝ) ≤ (n : ℝ)*(populationH (w n) t-populationH (w n) ((1+u)*t)) ∧
        a*u*(m : ℝ) ≤ (n : ℝ)*(populationH (w n) ((1-u)*t)-populationH (w n) t) := by
  obtain ⟨a, C, delta, M, ha, _, hd, hM, h⟩ := hp.right_quantile_moments
  refine ⟨a, delta, M, ha, hd, hM, ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  dsimp only
  intro u hu hu'
  exact populationH_mean_separation (hm.trans hmn) (w n)
    (rightQuantileTime_spec (w n) hm hmn).1 hu hu'
    (fun s hs hs' => (h grid w hw n m hm hmn hlarge hsmall s hs hs').1)

theorem PowerProfile.left_quantile_mean_separation {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ a delta M : ℝ, 0 < a ∧ 0 < delta ∧ 0 < M ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n m : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      let t := leftQuantileTime (w n) m
      ∀ u : ℝ, 0 < u → u ≤ 1/2 →
        a*u*(m : ℝ) ≤ (n : ℝ)*(populationG (w n) ((1+u)*t)-populationG (w n) t) ∧
        a*u*(m : ℝ) ≤ (n : ℝ)*(populationG (w n) t-populationG (w n) ((1-u)*t)) := by
  obtain ⟨a, C, delta, M, ha, _, hd, hM, h⟩ := hp.left_quantile_moments
  refine ⟨a, delta, M, ha, hd, hM, ?_⟩
  intro grid w hw n m hm hmn hlarge hsmall
  dsimp only
  intro u hu hu'
  exact populationG_mean_separation (hm.trans hmn) (w n)
    (leftQuantileTime_spec (w n) hm hmn).1 hu hu'
    (fun s hs hs' => (h grid w hw n m hm hmn hlarge hsmall s hs hs').1)

end Luce.Section6
