import Luce.Section6LeftSampledWeightedRow
import Luce.Section6RightSampledWeightedRow

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- An injective positive-depth map transfers a nonnegative sum to the full
finite depth interval. No estimate is assumed for the summed function. -/
theorem positive_depth_subset_sum_le {n : ℕ} (s : Finset (Fin n))
    (depth : Fin n → ℕ) (hinj : Function.Injective depth)
    (hdepth : ∀ j, 1 ≤ depth j ∧ depth j ≤ n)
    (F : ℕ → ℝ) (hF : ∀ h, 1 ≤ h → 0 ≤ F h) :
    (∑ j ∈ s, F (depth j)) ≤ ∑ h ∈ Finset.Ico 1 (n+1), F h := by
  classical
  have he : (∑ j ∈ s, F (depth j)) = ∑ h ∈ s.image depth, F h := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hinj hab
  have hsub : s.image depth ⊆ Finset.Ico 1 (n+1) := by
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_Ico.mpr ⟨(hdepth j).1, Nat.lt_succ_of_le (hdepth j).2⟩
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun h hh _ => hF h (Finset.mem_Ico.mp hh).1)

theorem PowerProfile.left_sampled_weighted_subset {f : ℝ → ℝ}
    {right : EndpointBehavior} {c alpha eta kappa d : ℝ}
    (hp : PowerProfile f (.power c alpha eta) right)
    (hk : kappa < alpha) (hd : 0 < d) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), ((i.val : ℝ)+1)/(n : ℝ) < delta → ∀ s : Finset (Fin n),
    (∑ j ∈ s, (((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa*
      ((w n).rate i*(((j.val : ℝ)+1)/(n : ℝ))^alpha/((j.val : ℝ)+1))*
      Real.exp (-(d*((w n).rate i*(((j.val : ℝ)+1)/(n : ℝ))^alpha)))) ≤ C := by
  obtain ⟨C, delta, hC, hdelta, hdelta1, hb⟩ := hp.left_sampled_ordinary_weighted_row hk hd
  refine ⟨C, delta, hC, hdelta, hdelta1, ?_⟩
  intro grid w hw n i hi s
  let F : ℕ → ℝ := fun h => (((i.val : ℝ)+1)/(h : ℝ))^kappa*
    ((w n).rate i*((h : ℝ)/(n : ℝ))^alpha/(h : ℝ))*
    Real.exp (-(d*((w n).rate i*((h : ℝ)/(n : ℝ))^alpha)))
  have hir := (w n).positive i
  have hinj : Function.Injective (fun j : Fin n => j.val+1) := by
    intro a b hab
    dsimp at hab
    apply Fin.ext
    omega
  have hh := positive_depth_subset_sum_le s (fun j => j.val+1) hinj
    (fun j => ⟨by omega, by omega⟩) F (fun h hh => by dsimp [F]; positivity)
  have hh' : (∑ j ∈ s, (((i.val : ℝ)+1)/((j.val : ℝ)+1))^kappa*
      ((w n).rate i*(((j.val : ℝ)+1)/(n : ℝ))^alpha/((j.val : ℝ)+1))*
      Real.exp (-(d*((w n).rate i*(((j.val : ℝ)+1)/(n : ℝ))^alpha)))) ≤
      ∑ h ∈ Finset.Ico 1 (n+1), F h := by
    simpa only [F, Nat.cast_add, Nat.cast_one] using hh
  exact hh'.trans (hb grid w hw n i hi n)

theorem PowerProfile.right_sampled_weighted_subset {f : ℝ → ℝ}
    {left : EndpointBehavior} {c beta eta kappa d : ℝ}
    (hp : PowerProfile f left (.power c beta eta))
    (hk : kappa < beta) (hd : 0 < d) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ (n : ℕ) (i : Fin n), (terminalDepth i : ℝ)/(n : ℝ) < delta → ∀ s : Finset (Fin n),
    (∑ j ∈ s, ((terminalDepth j : ℝ)/(terminalDepth i : ℝ))^kappa*
      ((w n).rate i*((n : ℝ)/(terminalDepth j : ℝ))^beta/(terminalDepth j : ℝ))*
      Real.exp (-(d*((w n).rate i*((n : ℝ)/(terminalDepth j : ℝ))^beta)))) ≤ C := by
  obtain ⟨C, delta, hC, hdelta, hdelta1, hb⟩ := hp.right_sampled_ordinary_weighted_row hk hd
  refine ⟨C, delta, hC, hdelta, hdelta1, ?_⟩
  intro grid w hw n i hi s
  let F : ℕ → ℝ := fun h => ((h : ℝ)/(terminalDepth i : ℝ))^kappa*
    ((w n).rate i*((n : ℝ)/(h : ℝ))^beta/(h : ℝ))*
    Real.exp (-(d*((w n).rate i*((n : ℝ)/(h : ℝ))^beta)))
  have hir := (w n).positive i
  have hinj : Function.Injective (terminalDepth : Fin n → ℕ) := by
    intro a b hab
    apply Fin.ext
    unfold terminalDepth at hab
    have ha := a.isLt
    have hb := b.isLt
    omega
  have hh := positive_depth_subset_sum_le s terminalDepth hinj
    (fun j => ⟨terminalDepth_pos j, Nat.sub_le _ _⟩) F
    (fun h hh => by dsimp [F]; positivity)
  exact hh.trans (hb grid w hw n i hi n)

end Luce.Section6
