import Luce.Section6GlobalUniformRow
import Luce.Section6RightSourceFullWeightedRow

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Global right weighted row: every source and every target. -/
theorem PowerProfile.global_right_weighted_insertion_row {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk0 : 0 ≤ kappa) (hk : kappa < beta) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal (((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, sigma, N1, hB, hsigma, hsigma1, hN1, hb⟩ := hp.right_source_full_weighted_insertion_row hk0 hk r p0 hp0
  obtain ⟨D, N2, hD, hN2, hd⟩ := hp.global_uniform_insertion_row r p0 hp0
  let W : ℝ := (1/sigma)^kappa
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨B+W*D, max N1 N2, add_pos hB (mul_pos hW hD), hN1.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n hn hlarge i s removed q p hpp hpp0 hs
  by_cases hi : (terminalDepth i : ℝ)/(n : ℝ) < sigma
  · exact (hb grid w hw n hn ((le_max_left _ _).trans hlarge) i hi s removed q p hpp hpp0 hs).trans
      (ENNReal.ofReal_le_ofReal (by have := mul_pos hW hD; linarith))
  · have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have ha : (0 : ℝ) < terminalDepth i := Nat.cast_pos.mpr (terminalDepth_pos i)
    have hi' := (le_div_iff₀ hnR).mp (le_of_not_gt hi)
    have hrow := hd grid w hw n hn ((le_max_right _ _).trans hlarge) i s removed q p hpp hpp0 hs
    calc
      _ ≤ ENNReal.ofReal W * (∑ j ∈ s,
          eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
            (p : ℝ≥0∞) (exponentialRace (w n))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        have hjn : (terminalDepth j : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n j.val)
        have hratio : (terminalDepth j : ℝ)/(terminalDepth i : ℝ) ≤ 1/sigma := by
          apply (div_le_div_iff₀ ha hsigma).mpr
          nlinarith [mul_le_mul_of_nonneg_left hjn hsigma.le]
        exact mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hratio hk0)) zero_le
      _ ≤ ENNReal.ofReal W * ENNReal.ofReal D := mul_le_mul_of_nonneg_left hrow zero_le
      _ = ENNReal.ofReal (W*D) := (ENNReal.ofReal_mul hW.le).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

/-- Global left weighted row: every source and every target. -/
theorem PowerProfile.global_left_weighted_insertion_row {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta kappa : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hk0 : 0 ≤ kappa) (hk : kappa < alpha) (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨B, delta, N1, hB, hd, hdh, hN1, hb⟩ := hp.left_endpoint_weighted_insertion_row hk0 hk r p0 hp0
  obtain ⟨D, N2, hD, hN2, hu⟩ := hp.global_uniform_insertion_row r p0 hp0
  let W : ℝ := (1/delta)^kappa
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨B+W*D, max N1 N2, add_pos hB (mul_pos hW hD), hN1.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n hn hlarge i s removed q p hpp hpp0 hs
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hin : (i.val : ℝ)+1 ≤ n := by exact_mod_cast (show i.val+1 ≤ n by omega)
  classical
  let P : Fin n → Prop := fun j => ((j.val : ℝ)+1)/(n : ℝ) ≤ delta
  let t := s.filter (fun j => ¬ P j)
  let g : Fin n → ℝ≥0∞ := fun j =>
    ENNReal.ofReal ((((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa)*
      eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
        (p : ℝ≥0∞) (exponentialRace (w n))
  have hnear : (∑ j ∈ s.filter P, g j) ≤ ENNReal.ofReal B := by
    apply hb grid w hw n hn ((le_max_left _ _).trans hlarge) i (s.filter P) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    exact ⟨hjP, hs j hjs⟩
  have hfar : (∑ j ∈ t, g j) ≤ ENNReal.ofReal (W*D) := by
    have hrow := hu grid w hw n hn ((le_max_right _ _).trans hlarge) i t removed q p hpp hpp0
      (fun j hj => hs j (Finset.mem_filter.mp hj).1)
    calc
      _ ≤ ENNReal.ofReal W * (∑ j ∈ t,
          eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
            (p : ℝ≥0∞) (exponentialRace (w n))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        have hjd := (lt_div_iff₀ hnR).mp (lt_of_not_ge (Finset.mem_filter.mp hj).2)
        have hjpos : 0 < (j.val : ℝ)+1 := by positivity
        have hratio : ((i.val : ℝ)+1)/((j.val : ℝ)+1) ≤ 1/delta := by
          apply (div_le_div_iff₀ hjpos hd).mpr
          nlinarith [mul_le_mul_of_nonneg_left hin hd.le]
        exact mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hratio hk0)) zero_le
      _ ≤ ENNReal.ofReal W * ENNReal.ofReal D := mul_le_mul_of_nonneg_left hrow zero_le
      _ = _ := (ENNReal.ofReal_mul hW.le).symm
  change (∑ j ∈ s, g j) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not s P g]
  exact (add_le_add hnear hfar).trans_eq (ENNReal.ofReal_add hB.le (mul_pos hW hD).le).symm

end Luce.Section6
