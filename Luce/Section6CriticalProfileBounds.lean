import Luce.Section6ProfileBounds
import Luce.Section6SamplingRelativeError

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

theorem CriticalProfile.global_comparison {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ s ∈ Ioo (0 : ℝ) 1,
      a/s ≤ f s ∧ f s ≤ b/s := by
  obtain ⟨hf,hpos,hc,heta,hex,hd,hr⟩ := hp
  let g : ℝ → ℝ := fun s => s*f s
  have hg : ContinuousOn g (Ioo (0 : ℝ) 1) := continuousOn_id.mul hf
  have hgpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < g s := fun s hs => mul_pos hs.1 (hpos s hs)
  have hleft : ∀ᶠ s in 𝓝[>] (0 : ℝ), c/2 ≤ g s ∧ g s ≤ 3*c/2 := by
    filter_upwards [hex.eventually_comparable hc heta, self_mem_nhdsWithin] with s hs hs0
    have hspos : 0 < s := hs0
    rw [Real.rpow_neg_one] at hs
    have h1 := mul_le_mul_of_nonneg_left hs.1 hspos.le
    have h2 := mul_le_mul_of_nonneg_left hs.2 hspos.le
    dsimp [g]
    constructor
    · have heq : s*(c/2*s⁻¹) = c/2 := by field_simp
      rwa [heq] at h1
    · have heq : s*(3*c/2*s⁻¹) = 3*c/2 := by field_simp
      rwa [heq] at h2
  have hright : ∀ᶠ s in 𝓝[>] (0 : ℝ), d/4 ≤ g (1-s) ∧ g (1-s) ≤ 2*d := by
    filter_upwards [finite_limit_eventually_bounds hd hr, self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds]
      with s hs hs0 hs1
    dsimp [g]
    constructor
    · have h := mul_le_mul_of_nonneg_left hs.1 (show 0 ≤ 1-s by linarith)
      nlinarith only [h,hs1,hd]
    · have h := mul_le_mul_of_nonneg_left hs.2 (show 0 ≤ 1-s by linarith)
      have hspos : 0 < s := hs0
      nlinarith only [h,hspos,hd]
  obtain ⟨a₁,ha₁,hlo₁⟩ := positive_continuous_lower_from_left hg hgpos
    ⟨c/2,by positivity,hleft.mono (fun _ h => h.1)⟩ (b := 1/2) (by norm_num) (by norm_num)
  obtain ⟨b₁,hb₁,hhi₁⟩ := positive_continuous_upper_from_left hg hgpos
    ⟨3*c/2,by positivity,hleft.mono (fun _ h => h.2)⟩ (b := 1/2) (by norm_num) (by norm_num)
  obtain ⟨a₂,ha₂,hlo₂⟩ := positive_continuous_lower_from_left (continuousOn_reflect hg)
    (positive_reflect hgpos) ⟨d/4,by positivity,hright.mono (fun _ h => h.1)⟩
    (b := 1/2) (by norm_num) (by norm_num)
  obtain ⟨b₂,hb₂,hhi₂⟩ := positive_continuous_upper_from_left (continuousOn_reflect hg)
    (positive_reflect hgpos) ⟨2*d,by positivity,hright.mono (fun _ h => h.2)⟩
    (b := 1/2) (by norm_num) (by norm_num)
  refine ⟨min a₁ a₂,max b₁ b₂,lt_min ha₁ ha₂,hb₁.trans_le (le_max_left _ _),?_⟩
  intro s hs
  have hgs : min a₁ a₂ ≤ g s ∧ g s ≤ max b₁ b₂ := by
    by_cases hmid : s ≤ 1/2
    · exact ⟨(min_le_left _ _).trans (hlo₁ s ⟨hs.1,hmid⟩),
        (hhi₁ s ⟨hs.1,hmid⟩).trans (le_max_left _ _)⟩
    · have hmem : 1-s ∈ Ioc (0 : ℝ) (1/2) := ⟨by linarith [hs.2],by linarith⟩
      have hl := hlo₂ (1-s) hmem
      have hu := hhi₂ (1-s) hmem
      simp only [sub_sub_cancel] at hl hu
      exact ⟨(min_le_right _ _).trans hl,hu.trans (le_max_right _ _)⟩
  exact ⟨(div_le_iff₀ hs.1).mpr (by simpa only [g,mul_comm] using hgs.1),
    (le_div_iff₀ hs.1).mpr (by simpa only [g,mul_comm] using hgs.2)⟩

theorem CriticalProfile.sampled_global_comparison {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ (n : ℕ) (i : Fin n),
        a*(n : ℝ)/((i.val : ℝ)+1) ≤ (w n).rate i ∧
        (w n).rate i ≤ b*(n : ℝ)/((i.val : ℝ)+1) := by
  obtain ⟨a,b,ha,hb,h⟩ := hp.global_comparison
  refine ⟨a,2*b,ha,by positivity,?_⟩
  intro grid w hw n i
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hi : (0 : ℝ) < (i.val : ℝ)+1 := by positivity
  have hs := samplePoint_mem grid i
  have hsample := h _ hs
  rw [hw n i]
  constructor
  · apply le_trans _ hsample.1
    calc
      _ = a/(((i.val : ℝ)+1)/(n : ℝ)) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left ha.le hs.1 (samplePoint_le_label grid i)
  · apply hsample.2.trans
    calc
      _ ≤ b/((((i.val : ℝ)+1)/(n : ℝ))/2) :=
        div_le_div_of_nonneg_left hb.le (by positivity)
          (by convert samplePoint_ge_half_label grid i using 1 <;> first | rfl | ring)
      _ = _ := by field_simp <;> ring

end Luce.Section6
