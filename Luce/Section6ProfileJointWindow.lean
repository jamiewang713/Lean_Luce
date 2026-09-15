import Luce.Section6ProfileGapQuantileTail
import Luce.Section6QuantileMeanLower
import Luce.Section6JointWindowProbability

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

theorem relative_window_budget {a C u m R : ℝ}
    (ha1 : a ≤ 1) (hC : 0 < C) (hu : 0 < u) (hm : 0 < m)
    (hu1 : u ≤ min (1/2) (1/(4*C))) (hbudget : 8*R ≤ a*u*m) :
    u ≤ 1/2 ∧ C*u ≤ 1/4 ∧ R ≤ m/4 ∧ R ≤ u*m := by
  have huhalf := hu1.trans (min_le_left _ _)
  have hum := mul_le_mul_of_nonneg_right huhalf hm.le
  have ham := mul_le_mul_of_nonneg_right ha1 (mul_pos hu hm).le
  have huc := (le_div_iff₀ (by positivity : 0 < 4*C)).mp (hu1.trans (min_le_right _ _))
  refine ⟨huhalf, by nlinarith only [huc], ?_, ?_⟩ <;>
    nlinarith only [hbudget, hum, ham, mul_pos hu hm]

/-- The polynomial time/weight window at the left endpoint. Constants
and every population premise are derived from the sampled profile. -/
theorem PowerProfile.left_joint_quantile_window {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) :
    ∃ a V K u0 delta M : ℝ,
      0 < a ∧ a ≤ 1 ∧ 0 < V ∧ 0 < K ∧ 0 < u0 ∧ u0 ≤ 1/2 ∧ 0 < delta ∧ 0 < M ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ n m r : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      ∀ removed : Finset (Fin n), removed.card ≤ r →
      ∀ q : Fin (Finset.univ \ removed).card, |(q.val : ℝ)-(m : ℝ)| ≤ r →
      ∀ u : ℝ, 0 < u → u ≤ u0 → 8*(r : ℝ) ≤ a*u*m →
        let t := leftQuantileTime (w n) m
        (exponentialRace (w n)).real {old |
          u < |raceGapStart (compactDeletedClocks removed old) q/t-1| ∨
          V*u < |raceGapRate (compactDeletedWeights (w n) removed)
            (compactDeletedClocks removed old) q/((n : ℝ)*populationD (w n) 1 t)-1|} ≤
          K/(u^2*(m : ℝ)) := by
  obtain ⟨a, dt, Mt, ha, ha1, hdt, hMt, htail⟩ := hp.left_gap_quantile_window
  obtain ⟨b, C, dw, Mw, hb, hC, hdw, _, hmom⟩ := hp.left_quantile_moments
  refine ⟨a, (C+3)/b, 4*(512/a^2)+2*C, min (1/2) (1/(4*C)), min dt dw,
    max Mt Mw, ha, ha1, by positivity, by positivity, by positivity,
    min_le_left _ _, lt_min hdt hdw, hMt.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n m r hm hmn hlarge hsmall removed hr q hq u hu hu0 hbudget
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hn := hm.trans hmn
  let t := leftQuantileTime (w n) m
  have ht : 0 < t := (leftQuantileTime_spec (w n) hm hmn).1
  have hbud := relative_window_budget ha1 hC hu hmR hu0 hbudget
  have hwin := hmom grid w hw n m hm hmn ((le_max_right _ _).trans hlarge)
    (hsmall.trans_le (min_le_right _ _))
  have hcentral : (n : ℝ)*populationG (w n) t = m := by
    rw [(leftQuantileTime_spec (w n) hm hmn).2]
    field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  have hloW := hwin ((1-u)*t) (by nlinarith [mul_pos hu ht, mul_le_mul_of_nonneg_right hbud.1 ht.le])
    (by nlinarith [mul_pos hu ht])
  have hcenterW := hwin t (by linarith) (by linarith)
  have hmeans := deleted_arrival_window_mean_lower (w n) hn removed hr hmR ht hu hbud.1
    hbud.2.1 hbud.2.2.1 hcentral hloW.2.1
  have htails := htail grid w hw n m r hm hmn ((le_max_left _ _).trans hlarge)
    (hsmall.trans_le (min_le_left _ _)) removed hr q hq u hu hbud.1 hbudget
  have hlow := htails.1.trans (quantile_exponential_tail_le_polynomial ha hu hmR hmeans.1)
  have hhigh := htails.2.trans (quantile_exponential_tail_le_polynomial ha hu hmR hmeans.2)
  exact deleted_joint_window_probability (w n) hn removed hr q hb hC.le hmR ht hu hbud.1
    hbud.2.2.2 hcenterW.1 (fun x hx => (hwin x hx.1 hx.2).2.2) hlow hhigh

/-- The polynomial time/weight window at the right endpoint, retaining
the small survivor population in the count tail. -/
theorem PowerProfile.right_joint_quantile_window {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) :
    ∃ a V K u0 delta M : ℝ,
      0 < a ∧ a ≤ 1 ∧ 0 < V ∧ 0 < K ∧ 0 < u0 ∧ u0 ≤ 1/2 ∧ 0 < delta ∧ 0 < M ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ n m r : ℕ, 0 < m → m < n → M ≤ (m : ℝ) → (m : ℝ)/(n : ℝ) < delta →
      ∀ removed : Finset (Fin n), removed.card ≤ r →
      ∀ q : Fin (Finset.univ \ removed).card,
        |((Finset.univ \ removed).card : ℝ)-(q.val : ℝ)-(m : ℝ)| ≤ r →
      ∀ u : ℝ, 0 < u → u ≤ u0 → 8*(r : ℝ) ≤ a*u*m →
        let t := rightQuantileTime (w n) m
        (exponentialRace (w n)).real {old |
          u < |raceGapStart (compactDeletedClocks removed old) q/t-1| ∨
          V*u < |raceGapRate (compactDeletedWeights (w n) removed)
            (compactDeletedClocks removed old) q/((n : ℝ)*populationD (w n) 1 t)-1|} ≤
          K/(u^2*(m : ℝ)) := by
  obtain ⟨a, dt, Mt, ha, ha1, hdt, hMt, htail⟩ := hp.right_gap_quantile_window
  obtain ⟨b, C, dw, Mw, hb, hC, hdw, _, hmom⟩ := hp.right_quantile_moments
  refine ⟨a, (C+3)/b, 4*(512/a^2)+2*C, min (1/2) (1/(4*C)), min dt dw,
    max Mt Mw, ha, ha1, by positivity, by positivity, by positivity,
    min_le_left _ _, lt_min hdt hdw, hMt.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n m r hm hmn hlarge hsmall removed hr q hq u hu hu0 hbudget
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hn := hm.trans hmn
  let t := rightQuantileTime (w n) m
  have ht : 0 < t := (rightQuantileTime_spec (w n) hm hmn).1
  have hbud := relative_window_budget ha1 hC hu hmR hu0 hbudget
  have hwin := hmom grid w hw n m hm hmn ((le_max_right _ _).trans hlarge)
    (hsmall.trans_le (min_le_right _ _))
  have hcentral : (n : ℝ)*populationH (w n) t = m := by
    rw [(rightQuantileTime_spec (w n) hm hmn).2]
    field_simp [ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  have hcenterW := hwin t (by linarith) (by linarith)
  have hmeans := deleted_survivor_window_mean_lower (w n) hn removed hr hmR ht hu hbud.1
    hbud.2.1 hbud.2.2.1 hcentral hcenterW.2.1
  have htails := htail grid w hw n m r hm hmn ((le_max_left _ _).trans hlarge)
    (hsmall.trans_le (min_le_left _ _)) removed hr q hq u hu hbud.1 hbudget
  have hlow := htails.1.trans (quantile_exponential_tail_le_polynomial ha hu hmR hmeans.1)
  have hhigh := htails.2.trans (quantile_exponential_tail_le_polynomial ha hu hmR hmeans.2)
  exact deleted_joint_window_probability (w n) hn removed hr q hb hC.le hmR ht hu hbud.1
    hbud.2.2.2 hcenterW.1 (fun x hx => (hwin x hx.1 hx.2).2.2) hlow hhigh

end Luce.Section6
