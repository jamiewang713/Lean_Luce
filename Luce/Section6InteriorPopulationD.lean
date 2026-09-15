import Luce.Section6InteriorRemainingRate
import Luce.Section6PopulationFinite

noncomputable section
open scoped BigOperators
namespace Luce.Section6

/-- Explicitly count a block away from both ends of the label set. -/
theorem exists_interior_label_block {n : ℕ} (hn : 8 ≤ n) :
    ∃ B : Finset (Fin n), (n : ℝ)/8 ≤ (B.card : ℝ) ∧
      ∀ i ∈ B, (1/4 : ℝ) ≤ ((i.val : ℝ)+1)/(n : ℝ) ∧
        (1/4 : ℝ) ≤ ((i.rev.val : ℝ)+1)/(n : ℝ) := by
  classical
  let k := n/4
  let e : Fin k ↪ Fin n := ⟨fun i => ⟨i.val+k, by dsimp [k] at *; omega⟩,
    fun i j h => by apply Fin.ext; have hh := congrArg Fin.val h; dsimp at hh; omega⟩
  refine ⟨Finset.univ.map e, ?_, ?_⟩
  · simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hk : n ≤ 8*k := by dsimp [k]; omega
    have hkR : (n : ℝ) ≤ 8*(k : ℝ) := by exact_mod_cast hk
    linarith
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have heval : (e j).val = j.val+k := rfl
    have hleft : n ≤ 4*((e j).val+1) := by rw [heval]; dsimp [k]; omega
    have hright : n ≤ 4*((e j).rev.val+1) := by
      simp only [Fin.val_rev, heval]
      dsimp [k]
      have hj := j.isLt
      dsimp [k] at hj
      omega
    have hlR : (n : ℝ) ≤ 4*((e j).val+1 : ℝ) := by exact_mod_cast hleft
    have hrR : (n : ℝ) ≤ 4*((e j).rev.val+1 : ℝ) := by exact_mod_cast hright
    constructor <;> apply (le_div_iff₀ hnR).mpr <;> linarith

theorem populationD_one_upper {n : ℕ} (hn : 0 < n) (w : Weights n)
    {t : ℝ} (ht : 0 < t) : populationD w 1 t ≤ Real.exp (-1)/t := by
  unfold populationD
  simp only [pow_one]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn : (0 : ℝ) < n)).mpr
  calc
    _ ≤ ∑ _i : Fin n, Real.exp (-1)/t :=
      Finset.sum_le_sum fun _ _ => rateKernel_le_exp_neg_one_div ht
    _ = _ := by simp; ring

/-- Compact positive times have a uniform positive weighted population.
Only continuity and positivity of the profile are needed. -/
theorem interior_populationD_bounds {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 1))
    (hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x)
    {s T : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
    ∀ n : ℕ, 8 ≤ n → ∀ t : ℝ, s ≤ t → t ≤ T →
      a ≤ populationD (w n) 1 t ∧ populationD (w n) 1 t ≤ C := by
  classical
  obtain ⟨d, M, hd, hM, hrate⟩ := interior_sampled_rate_bounds hf hpos
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) < 1)
  let b := d*Real.exp (-(T*M))
  have hb : 0 < b := mul_pos hd (Real.exp_pos _)
  refine ⟨b/8, Real.exp (-1)/s, by positivity, by positivity, ?_⟩
  intro grid w hw n hn t hst htT
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have ht : 0 < t := hs.trans_le hst
  obtain ⟨B, hcard, hlabels⟩ := exists_interior_label_block hn
  have hterm (i : Fin n) (hi : i ∈ B) : b ≤ rateKernel t ((w n).rate i) := by
    obtain ⟨hl, hu⟩ := hrate grid w hw n i (hlabels i hi).1 (hlabels i hi).2
    have hex : Real.exp (-(T*M)) ≤ survivalKernel t ((w n).rate i) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul hu htT ht.le hM.le
      nlinarith
    exact mul_le_mul hl hex (Real.exp_pos _).le ((w n).positive i).le
  constructor
  · apply (le_div_iff₀ hnR).mpr
    change (b/8)*(n : ℝ) ≤ ∑ i : Fin n, (w n).rate i^1*survivalKernel t ((w n).rate i)
    simp only [pow_one]
    calc
      _ = ((n : ℝ)/8)*b := by ring
      _ ≤ (B.card : ℝ)*b := mul_le_mul_of_nonneg_right hcard hb.le
      _ = ∑ _i ∈ B, b := by simp
      _ ≤ ∑ i ∈ B, rateKernel t ((w n).rate i) := Finset.sum_le_sum hterm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        (fun i _ _ => rateKernel_nonneg ((w n).positive i).le)
  · exact (populationD_one_upper hn0 (w n) ht).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le hs hst)

end Luce.Section6
