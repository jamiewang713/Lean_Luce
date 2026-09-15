import Luce.Section6RandomWeightConcentration

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace Luce.Section6

/-- Joint control of the actual gap start and the actual remaining
weight. The free window width will subsequently be set to h^(-1/4). -/
theorem deleted_joint_window_probability {n r : ℕ} (w : Weights n) (hn : 0 < n)
    (removed : Finset (Fin n)) (hr : removed.card ≤ r)
    (q : Fin (Finset.univ \ removed).card) {a C J m t u : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hm : 0 < m) (ht : 0 < t)
    (hu : 0 < u) (hu1 : u ≤ 1/2) (hrm : (r : ℝ) ≤ u*m)
    (hlower : a*m/t ≤ (n : ℝ)*populationD w 1 t)
    (hsecond : ∀ x ∈ Icc (t/4) (4*t), (n : ℝ)*populationD w 2 x ≤ C*m/t^2)
    (hlo : (exponentialRace w).real {old | raceGapStart (compactDeletedClocks removed old) q < (1-u)*t} ≤ J/(u^2*m))
    (hhi : (exponentialRace w).real {old | (1+u)*t < raceGapStart (compactDeletedClocks removed old) q} ≤ J/(u^2*m)) :
    (exponentialRace w).real {old |
      u < |raceGapStart (compactDeletedClocks removed old) q/t-1| ∨
      ((C+3)/a)*u < |raceGapRate (compactDeletedWeights w removed)
        (compactDeletedClocks removed old) q/((n : ℝ)*populationD w 1 t)-1|} ≤
        (4*J+2*C)/(u^2*m) := by
  let mu := (n : ℝ)*populationD w 1 t
  have hmu : 0 < mu := (div_pos (mul_pos ha hm) ht).trans_le hlower
  let A := {old | raceGapStart (compactDeletedClocks removed old) q < (1-u)*t}
  let B := {old | (1+u)*t < raceGapStart (compactDeletedClocks removed old) q}
  let D := {old | u*m/t+(C*u*m/t+2*(r : ℝ)/t) <
    |raceGapRate (compactDeletedWeights w removed) (compactDeletedClocks removed old) q-mu|}
  have hthreshold : u*m/t+(C*u*m/t+2*(r : ℝ)/t) ≤ (((C+3)/a)*u)*mu := by
    have hr' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrm (by norm_num : (0 : ℝ) ≤ 2)) ht.le
    have hl' := mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ ((C+3)/a)*u)
    have hid : (((C+3)/a)*u)*(a*m/t) = (C+3)*u*m/t := by field_simp
    rw [hid] at hl'
    calc
      _ ≤ u*m/t+(C*u*m/t+2*(u*m)/t) := add_le_add le_rfl (add_le_add le_rfl hr')
      _ = (C+3)*u*m/t := by ring
      _ ≤ _ := hl'
  have hinc : {old | u < |raceGapStart (compactDeletedClocks removed old) q/t-1| ∨
      ((C+3)/a)*u < |raceGapRate (compactDeletedWeights w removed)
        (compactDeletedClocks removed old) q/mu-1|} ⊆ (A ∪ B) ∪ D := by
    intro old hold
    rcases hold with hbad | hbad
    · apply Or.inl
      by_contra hnot
      simp only [A, B, mem_union, mem_ofPred_eq, not_or, not_lt] at hnot
      have hlo' := (le_div_iff₀ ht).mpr hnot.1
      have hhi' := (div_le_iff₀ ht).mpr hnot.2
      have habs : |raceGapStart (compactDeletedClocks removed old) q/t-1| ≤ u := by
        rw [abs_le]
        constructor <;> linarith only [hlo', hhi']
      exact not_lt_of_ge habs hbad
    · apply Or.inr
      rw [div_sub_one hmu.ne', abs_div, abs_of_pos hmu] at hbad
      exact hthreshold.trans_lt ((lt_div_iff₀ hmu).mp hbad)
  have hweight := deleted_weight_quantile_window_probability w hn removed hr q hC hm ht hu hu hu1 hsecond
  calc
    _ ≤ (exponentialRace w).real ((A ∪ B) ∪ D) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hinc)
    _ ≤ (exponentialRace w).real (A ∪ B)+(exponentialRace w).real D := measureReal_union_le _ _
    _ ≤ ((exponentialRace w).real A+(exponentialRace w).real B)+(exponentialRace w).real D :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ (J/(u^2*m)+J/(u^2*m))+
        ((J/(u^2*m)+J/(u^2*m))+2*C/(u^2*m)) :=
      add_le_add (add_le_add hlo hhi) (hweight.trans (add_le_add (add_le_add hlo hhi) le_rfl))
    _ = _ := by ring

end Luce.Section6
