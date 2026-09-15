import Luce.Section6RandomWeightProbability
import Luce.Section6DeletedWeightDrift

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- Concentration of the actual random-gap weight about the original
central population mean. Both endpoint mean errors are discharged by
finite deletion and derivative estimates. The time-window probabilities
are actual terms in the bound, not assumed concentration estimates. -/
theorem deleted_weight_quantile_window_probability {n r : ℕ} (w : Weights n)
    (hn : 0 < n) (removed : Finset (Fin n)) (hr : removed.card ≤ r)
    (q : Fin (Finset.univ \ removed).card) {C m t eps u : ℝ}
    (hC : 0 ≤ C) (hm : 0 < m) (ht : 0 < t) (heps : 0 < eps)
    (hu : 0 < u) (hu1 : u ≤ 1/2)
    (hsecond : ∀ x ∈ Icc (t/4) (4*t), (n : ℝ)*populationD w 2 x ≤ C*m/t^2) :
    (exponentialRace w).real {old | eps*m/t+(C*u*m/t+2*(r : ℝ)/t) <
      |raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) q-
        (n : ℝ)*populationD w 1 t|} ≤
      (exponentialRace w).real {old | raceGapStart (compactDeletedClocks removed old) q < (1-u)*t} +
      (exponentialRace w).real {old | (1+u)*t < raceGapStart (compactDeletedClocks removed old) q} +
      2*C/(eps^2*m) := by
  have hut : 0 ≤ u*t := (mul_pos hu ht).le
  have hlo : (1-u)*t ∈ Icc (t/2) (2*t) := by
    constructor <;> nlinarith only [hu1, hut, ht, mul_le_mul_of_nonneg_right hu1 ht.le]
  have hhi : (1+u)*t ∈ Icc (t/2) (2*t) := by
    constructor <;> nlinarith only [hu1, hut, ht, mul_le_mul_of_nonneg_right hu1 ht.le]
  have hdlo : |(1-u)*t-t| ≤ u*t := by
    rw [show (1-u)*t-t = -(u*t) by ring, abs_neg, abs_of_nonneg hut]
  have hdhi : |(1+u)*t-t| ≤ u*t := by
    rw [show (1+u)*t-t = u*t by ring, abs_of_nonneg hut]
  have hb := random_gap_weight_probability_bound w hn removed q
    ((half_pos ht).le.trans hlo.1) ((half_pos ht).le.trans hhi.1)
    (div_pos (mul_pos heps hm) ht)
    (deleted_weight_mean_drift w hn removed hr hC hm.le ht hsecond hlo hdlo)
    (deleted_weight_mean_drift w hn removed hr hC hm.le ht hsecond hhi hdhi)
  have hl : (n : ℝ)*deletedD w removed 2 ((1-u)*t) ≤ C*m/t^2 :=
    (mul_le_mul_of_nonneg_left (deletedD_le_populationD w removed 2 _) (Nat.cast_nonneg n)).trans
      (hsecond _ ⟨by linarith [hlo.1], by linarith [hlo.2]⟩)
  have hh : (n : ℝ)*deletedD w removed 2 ((1+u)*t) ≤ C*m/t^2 :=
    (mul_le_mul_of_nonneg_left (deletedD_le_populationD w removed 2 _) (Nat.cast_nonneg n)).trans
      (hsecond _ ⟨by linarith [hhi.1], by linarith [hhi.2]⟩)
  apply hb.trans
  apply add_le_add le_rfl
  calc
    _ ≤ (C*m/t^2+C*m/t^2)/(eps*m/t)^2 :=
      div_le_div_of_nonneg_right (add_le_add hl hh) (sq_nonneg _)
    _ = 2*C/(eps^2*m) := by field_simp; ring

end Luce.Section6
