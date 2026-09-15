import Luce.Section6EndpointUniformRows
import Luce.Section6InteriorUniformRow

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Uniform unweighted insertion row over every target and every source,
for either allowed endpoint behavior and both sampling grids. -/
theorem PowerProfile.global_uniform_insertion_row {f : ℝ → ℝ}
    {left right : EndpointBehavior} (hp : PowerProfile f left right)
    (r p0 : ℕ) (hp0 : 0 < p0) :
    ∃ C N : ℝ, 0 < C ∧ 0 < N ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 0 < n → N ≤ (n : ℝ) →
    ∀ (i : Fin n) (s : Finset (Fin n)) (removed : Fin n → Finset (Fin n))
      (q : Fin n → ℕ) (p : ℕ), 1 ≤ p → p ≤ p0 →
    (∀ j ∈ s, (removed j).card ≤ r ∧ Nat.dist (q j) j.val ≤ r+1) →
    (∑ j ∈ s, eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n))) ≤ ENNReal.ofReal C := by
  obtain ⟨A, dl, Nl, hA, hdl, hdlh, hNl, hl⟩ := hp.left_endpoint_uniform_row r p0 hp0
  obtain ⟨B, dr, Nr, hB, hdr, hdrh, hNr, hr⟩ := hp.right_endpoint_uniform_row r p0 hp0
  let eps : ℝ := min dl (dr/2)
  have heps : 0 < eps := lt_min hdl (half_pos hdr)
  obtain ⟨D, Nm, hD, hNm, hm⟩ := hp.interior_insertion_uniform_row heps r p0 hp0
  refine ⟨A+(B+D), max Nl (max Nr (max Nm (2/dr))), add_pos hA (add_pos hB hD),
    hNl.trans_le (le_max_left _ _), ?_⟩
  intro grid w hw n hn hlarge i s removed q p hpp hpp0 hs
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnl : Nl ≤ (n : ℝ) := (le_max_left _ _).trans hlarge
  have hnr : Nr ≤ (n : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hrest : max Nm (2/dr) ≤ (n : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hnm : Nm ≤ (n : ℝ) := (le_max_left _ _).trans hrest
  have hmargin : 2 ≤ dr*(n : ℝ) := by
    have hh := (div_le_iff₀ hdr).mp ((le_max_right _ _).trans hrest)
    nlinarith
  classical
  let P : Fin n → Prop := fun j => ((j.val : ℝ)+1)/(n : ℝ) ≤ dl
  let Q : Fin n → Prop := fun j => (terminalDepth j : ℝ)/(n : ℝ) ≤ dr
  let t := s.filter (fun j => ¬ P j)
  let g : Fin n → ℝ≥0∞ := fun j =>
    eLpNorm (fun old => (deletedGapKernel (w n) (removed j) old i (q j)).toReal)
      (p : ℝ≥0∞) (exponentialRace (w n))
  have hleft : (∑ j ∈ s.filter P, g j) ≤ ENNReal.ofReal A := by
    apply hl grid w hw n hn hnl i (s.filter P) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hj
    exact ⟨hjP, hs j hjs⟩
  have hright : (∑ j ∈ t.filter Q, g j) ≤ ENNReal.ofReal B := by
    apply hr grid w hw n hn hnr i (t.filter Q) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjt, hjQ⟩ := Finset.mem_filter.mp hj
    exact ⟨hjQ, hs j (Finset.mem_filter.mp hjt).1⟩
  have hmiddle : (∑ j ∈ t.filter (fun j => ¬ Q j), g j) ≤ ENNReal.ofReal D := by
    apply hm grid w hw n hn hnm i (t.filter (fun j => ¬ Q j)) removed q p hpp hpp0
    intro j hj
    obtain ⟨hjt, hjQ⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjs, hjP⟩ := Finset.mem_filter.mp hjt
    have hlow := (lt_div_iff₀ hnR).mp (lt_of_not_ge hjP)
    have hhigh := (lt_div_iff₀ hnR).mp (lt_of_not_ge hjQ)
    have hterminal : (terminalDepth j : ℝ) = (n : ℝ)-(j.val : ℝ) := by
      unfold terminalDepth
      rw [Nat.cast_sub j.isLt.le]
    rw [hterminal] at hhigh
    have hel : eps ≤ dl := min_le_left _ _
    have her : eps ≤ dr/2 := min_le_right _ _
    refine ⟨?_, ?_, hs j hjs⟩
    · nlinarith [mul_le_mul_of_nonneg_right hel hnR.le]
    · nlinarith [mul_le_mul_of_nonneg_right her hnR.le]
  have htail : (∑ j ∈ t, g j) ≤ ENNReal.ofReal (B+D) := by
    rw [← Finset.sum_filter_add_sum_filter_not t Q g]
    exact (add_le_add hright hmiddle).trans_eq (ENNReal.ofReal_add hB.le hD.le).symm
  change (∑ j ∈ s, g j) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not s P g]
  exact (add_le_add hleft htail).trans_eq (ENNReal.ofReal_add hA.le (add_pos hB hD).le).symm

end Luce.Section6
