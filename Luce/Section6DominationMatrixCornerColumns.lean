import Luce.Section6DominationMatrixCornerEnvelope
import Luce.Section6CornerEnvelopeColumns
import Luce.Section6SampledWeightedSubsets

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Same-right-corner source contribution to a column of the concrete
matrix. The derived lower target-depth cutoff is still explicit. -/
theorem PowerProfile.domination_matrix_right_corner_column {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta : ℝ}
    (hp : PowerProfile f left (.power c beta eta)) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C H delta : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ j : Fin n, H ≤ (terminalDepth j : ℝ) →
      (terminalDepth j : ℝ)/(n : ℝ) ≤ delta →
    ∀ s : Finset (Fin n), (∀ i ∈ s, (terminalDepth i : ℝ)/(n : ℝ) ≤ delta) →
      (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨B, d, nu, H, delta, hB, hd, hnu, hH, hdelta, hdelta1, hb⟩ :=
    hp.domination_matrix_right_corner_envelope r p hp1 1 zero_lt_one le_rfl
  obtain ⟨D, hD, hsum⟩ := right_corner_envelope_column_bound
    hp.2.2.2.1.2.1 zero_lt_one hd hnu
  refine ⟨B*D, H, delta, mul_pos hB hD, hH, hdelta, hdelta1, ?_⟩
  intro grid w hw n j hjH hj s hs
  let F : ℕ → ℝ := fun a =>
    (((a : ℝ)/(terminalDepth j : ℝ))^beta/(terminalDepth j : ℝ))*
      Real.exp (-d*((a : ℝ)/(terminalDepth j : ℝ))^beta)+
      exceptionalEnvelope beta 1 d nu a (terminalDepth j)
  have hF (a : ℕ) (_ha : 1 ≤ a) : 0 ≤ F a := by
    dsimp [F]
    exact add_nonneg (by positivity) (exceptionalEnvelope_nonneg _ _ _ _ _ _)
  have hinj : Function.Injective (terminalDepth : Fin n → ℕ) := by
    intro a b hab
    apply Fin.ext
    unfold terminalDepth at hab
    have := a.isLt
    have := b.isLt
    omega
  have hfinite := positive_depth_subset_sum_le s terminalDepth hinj
    (fun i => ⟨terminalDepth_pos i, Nat.sub_le _ _⟩) F hF
  have htotal : (∑ i ∈ s, F (terminalDepth i)) ≤ D :=
    hfinite.trans (hsum (terminalDepth j) (terminalDepth_pos j) n)
  calc
    _ ≤ ∑ i ∈ s, B*F (terminalDepth i) :=
      Finset.sum_le_sum (fun i hi => hb grid w hw n i j hjH hj (hs i hi))
    _ = B*(∑ i ∈ s, F (terminalDepth i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ B*D := mul_le_mul_of_nonneg_left htotal hB.le

/-- Same-left-corner source contribution, using the transposed exceptional
column estimate and retaining the derived target-depth cutoff. -/
theorem PowerProfile.domination_matrix_left_corner_column {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right) (r p : ℕ) (hp1 : 0 < p) :
    ∃ C H delta : ℝ, 0 < C ∧ 0 < H ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, ∀ j : Fin n, H ≤ (j.val : ℝ)+1 → ((j.val : ℝ)+1)/(n : ℝ) ≤ delta →
    ∀ s : Finset (Fin n), (∀ i ∈ s, ((i.val : ℝ)+1)/(n : ℝ) ≤ delta) →
      (∑ i ∈ s, insertionDominationMatrix (w n) r p i j) ≤ C := by
  obtain ⟨B, d, nu, H, delta, hB, hd, hnu, hH, hdelta, hdelta1, hb⟩ :=
    hp.domination_matrix_left_corner_envelope r p hp1 1 zero_lt_one le_rfl
  obtain ⟨D, hD, hsum⟩ := left_corner_envelope_column_bound
    hp.2.2.1.2.1 zero_lt_one hd hnu
  refine ⟨B*D, H, delta, mul_pos hB hD, hH, hdelta, hdelta1, ?_⟩
  intro grid w hw n j hjH hj s hs
  let F : ℕ → ℝ := fun a =>
    ((((j.val : ℝ)+1)/(a : ℝ))^alpha/((j.val : ℝ)+1))*
      Real.exp (-d*(((j.val : ℝ)+1)/(a : ℝ))^alpha)+
      exceptionalEnvelope alpha 1 d nu (j.val+1) a
  have hF (a : ℕ) (_ha : 1 ≤ a) : 0 ≤ F a := by
    dsimp [F]
    exact add_nonneg (by positivity) (exceptionalEnvelope_nonneg _ _ _ _ _ _)
  have hinj : Function.Injective (fun i : Fin n => i.val+1) := by
    intro a b hab
    apply Fin.ext
    change a.val+1 = b.val+1 at hab
    omega
  have hfinite := positive_depth_subset_sum_le s (fun i => i.val+1) hinj
    (fun i => ⟨by omega, Nat.succ_le_of_lt i.isLt⟩) F hF
  have htotal : (∑ i ∈ s, F (i.val+1)) ≤ D := hfinite.trans (by
    simpa only [F, Nat.cast_add, Nat.cast_one] using hsum (j.val+1) (by omega) n)
  calc
    _ ≤ ∑ i ∈ s, B*F (i.val+1) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [F, Nat.cast_add, Nat.cast_one] using hb grid w hw n i j hjH hj (hs i hi)
    _ = B*(∑ i ∈ s, F (i.val+1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ B*D := mul_le_mul_of_nonneg_left htotal hB.le

end Luce.Section6
