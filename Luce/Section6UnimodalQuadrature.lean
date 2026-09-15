import Luce.Section6MonotoneQuadrature

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem monotone_sample_average_error (grid : SamplingGrid) {n : ℕ} (hn : 0 < n)
    {g : ℝ → ℝ} (hg : MonotoneOn g (Icc (0 : ℝ) 1)) :
    |(∑ i : Fin n, g (samplePoint grid n i))/(n : ℝ) - ∫ x in (0 : ℝ)..1, g x| ≤
      (g 1-g 0)/(n : ℝ) := by
  have h := antitone_sample_average_error grid hn hg.neg
  simp only [Finset.sum_neg_distrib, neg_div, intervalIntegral.integral_neg] at h
  have heq : -((∑ i : Fin n, g (samplePoint grid n i))/(n : ℝ)) -
      -(∫ x in (0 : ℝ)..1, g x) =
      -((∑ i : Fin n, g (samplePoint grid n i))/(n : ℝ) - ∫ x in (0 : ℝ)..1, g x) := by ring
  have heq' : -g 0 - -g 1 = g 1-g 0 := by ring
  rw [heq, abs_neg, heq'] at h
  exact h

theorem monotoneOn_clip_min {g : ℝ → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (_hc1 : c ≤ 1)
    (hg : MonotoneOn g (Icc 0 c)) :
    MonotoneOn (fun x => g (min x c)) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  exact hg ⟨le_min hx.1 hc0, min_le_right _ _⟩
    ⟨le_min hy.1 hc0, min_le_right _ _⟩ (min_le_min_right c hxy)

theorem antitoneOn_clip_max {g : ℝ → ℝ} {c : ℝ} (_hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hg : AntitoneOn g (Icc c 1)) :
    AntitoneOn (fun x => g (max x c)) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  exact hg ⟨le_max_right _ _, max_le hx.2 hc1⟩
    ⟨le_max_right _ _, max_le hy.2 hc1⟩ (max_le_max_right c hxy)

theorem clipped_unimodal_identity (g : ℝ → ℝ) (c x : ℝ) :
    g x = g (min x c) + g (max x c) - g c := by
  rcases le_total x c with h | h
  · rw [min_eq_left h, max_eq_right h]
    ring
  · rw [min_eq_right h, max_eq_left h]
    ring

/-- Quadrature for an envelope with one maximum. This hypothesis is used
only for explicit analytic envelopes, never imposed on the sampled profile. -/
theorem unimodal_sample_average_error (grid : SamplingGrid) {n : ℕ} (hn : 0 < n)
    {g : ℝ → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hup : MonotoneOn g (Icc 0 c)) (hdown : AntitoneOn g (Icc c 1)) :
    |(∑ i : Fin n, g (samplePoint grid n i))/(n : ℝ) - ∫ x in (0 : ℝ)..1, g x| ≤
      (2*g c-g 0-g 1)/(n : ℝ) := by
  let u : ℝ → ℝ := fun x => g (min x c)
  let v : ℝ → ℝ := fun x => g (max x c)
  have hu : MonotoneOn u (Icc (0 : ℝ) 1) := monotoneOn_clip_min hc0 hc1 hup
  have hv : AntitoneOn v (Icc (0 : ℝ) 1) := antitoneOn_clip_max hc0 hc1 hdown
  have hui : IntervalIntegrable u volume 0 1 :=
    (show MonotoneOn u (uIcc 0 1) by simpa using hu).intervalIntegrable
  have hvi : IntervalIntegrable v volume 0 1 :=
    (show AntitoneOn v (uIcc 0 1) by simpa using hv).intervalIntegrable
  have heq : g = fun x => u x + v x - g c := by
    funext x
    exact clipped_unimodal_identity g c x
  have hint : (∫ x in (0 : ℝ)..1, g x) =
      (∫ x in (0 : ℝ)..1, u x) + (∫ x in (0 : ℝ)..1, v x) - g c := by
    conv_lhs => rw [heq]
    rw [intervalIntegral.integral_sub (hui.add hvi) intervalIntegrable_const,
      intervalIntegral.integral_add hui hvi]
    simp
  have hsum : (∑ i : Fin n, g (samplePoint grid n i))/(n : ℝ) =
      (∑ i : Fin n, u (samplePoint grid n i))/(n : ℝ) +
      (∑ i : Fin n, v (samplePoint grid n i))/(n : ℝ) - g c := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    conv_lhs => rw [heq]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_div, add_div,
      mul_div_cancel_left₀ _ hn0]
  have hU := monotone_sample_average_error grid hn hu
  have hV := antitone_sample_average_error grid hn hv
  have hv0 : v 0 = g c := by simp [v, max_eq_right hc0]
  have hv1 : v 1 = g 1 := by simp [v, max_eq_left hc1]
  have hu0 : u 0 = g 0 := by simp [u, min_eq_left hc0]
  have hu1 : u 1 = g c := by simp [u, min_eq_right hc1]
  rw [hv0, hv1] at hV
  rw [hu0, hu1] at hU
  rw [hsum, hint]
  have he : ((∑ i : Fin n, u (samplePoint grid n i))/(n : ℝ) +
      (∑ i : Fin n, v (samplePoint grid n i))/(n : ℝ) - g c) -
      ((∫ x in (0 : ℝ)..1, u x) + (∫ x in (0 : ℝ)..1, v x) - g c) =
      ((∑ i : Fin n, u (samplePoint grid n i))/(n : ℝ) - ∫ x in (0 : ℝ)..1, u x) +
      ((∑ i : Fin n, v (samplePoint grid n i))/(n : ℝ) - ∫ x in (0 : ℝ)..1, v x) := by ring
  rw [he]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ (g c-g 0)/(n : ℝ) + (g c-g 1)/(n : ℝ) := add_le_add hU hV
    _ = _ := by ring

end Luce.Section6
