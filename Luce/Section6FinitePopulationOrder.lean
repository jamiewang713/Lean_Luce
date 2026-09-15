import Luce.Section6PopulationDerivatives
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace Luce.Section6

theorem populationD_pos {n : ℕ} (hn : 0 < n) (w : Weights n) (r : ℕ) (t : ℝ) :
    0 < populationD w r t := by
  unfold populationD
  apply div_pos _ (Nat.cast_pos.mpr hn)
  apply Finset.sum_pos'
  · intro i _
    exact (mul_pos (pow_pos (w.positive i) r) (survivalKernel_pos t (w.rate i))).le
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _, mul_pos (pow_pos (w.positive _) r) (survivalKernel_pos _ _)⟩

theorem populationD_antitone {n : ℕ} (w : Weights n) (r : ℕ) :
    Antitone (populationD w r) := by
  intro s t hst
  unfold populationD
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (pow_pos (w.positive i) r).le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hst) (w.positive i).le

theorem populationH_zero {n : ℕ} (hn : 0 < n) (w : Weights n) : populationH w 0 = 1 := by
  simp [populationH, survivalKernel, (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

theorem populationG_zero {n : ℕ} (w : Weights n) : populationG w 0 = 0 := by
  simp [populationG, survivalKernel]

theorem populationH_strictAnti {n : ℕ} (hn : 0 < n) (w : Weights n) :
    StrictAnti (populationH w) := by
  apply strictAnti_of_deriv_neg
  intro t
  rw [(populationH_hasDerivAt w t).deriv]
  exact neg_neg_of_pos (populationD_pos hn w 1 t)

theorem populationG_strictMono {n : ℕ} (hn : 0 < n) (w : Weights n) :
    StrictMono (populationG w) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(populationG_hasDerivAt hn w t).deriv]
  exact populationD_pos hn w 1 t

theorem populationH_tendsto_zero {n : ℕ} (w : Weights n) :
    Tendsto (populationH w) atTop (𝓝 0) := by
  have hi (i : Fin n) : Tendsto (fun t : ℝ => survivalKernel t (w.rate i)) atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => t*w.rate i) atTop atTop :=
      (tendsto_mul_const_atTop_of_pos (w.positive i)).mpr tendsto_id
    simpa only [Function.comp_def, survivalKernel, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hh := (tendsto_finsetSum Finset.univ (fun i _ => hi i)).div_const (n : ℝ)
  change Tendsto (fun t => (∑ i, survivalKernel t (w.rate i))/(n : ℝ)) atTop (𝓝 0)
  simpa only [Finset.sum_const_zero, zero_div] using hh

theorem populationG_tendsto_one {n : ℕ} (hn : 0 < n) (w : Weights n) :
    Tendsto (populationG w) atTop (𝓝 1) := by
  have he : populationG w = fun t => 1-populationH w t :=
    funext (populationG_eq_one_sub_H hn w)
  rw [he]
  simpa only [sub_zero] using (populationH_tendsto_zero w).const_sub 1

theorem exists_populationG_eq {n : ℕ} (hn : 0 < n) (w : Weights n) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) : ∃ t ∈ Ici (0 : ℝ), populationG w t = x := by
  obtain ⟨T, hT0, hTx⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    ((populationG_tendsto_one hn w).eventually (lt_mem_nhds hx.2))).exists
  have hc : Continuous (populationG w) :=
    continuous_iff_continuousAt.mpr (fun t => (populationG_hasDerivAt hn w t).continuousAt)
  obtain ⟨t, ht, htx⟩ := intermediate_value_Icc hT0 hc.continuousOn
    (show x ∈ Icc (populationG w 0) (populationG w T) from
      ⟨by simpa only [populationG_zero] using hx.1, hTx.le⟩)
  exact ⟨t, ht.1, htx⟩

end Luce.Section6
