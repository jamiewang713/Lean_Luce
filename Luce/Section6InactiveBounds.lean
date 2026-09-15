import Luce.Section6ProfileBounds

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

theorem PowerProfile.global_upper_of_left_finite {f : ℝ → ℝ}
    {right : EndpointBehavior} {c : ℝ} (h : PowerProfile f (.finite c) right) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Ioo (0 : ℝ) 1, f x ≤ M := by
  have hl := h.2.2.1
  have hn : ∃ M : ℝ, 0 < M ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), f s ≤ M :=
    ⟨2*c, by dsimp [LeftBehavior] at hl; linarith [hl.1],
      (finite_limit_eventually_bounds hl.1 hl.2).mono fun _ hs => hs.2⟩
  obtain ⟨Ml, hMl, hbL⟩ := positive_continuous_upper_from_left h.1 h.2.1 hn
    (b := 1/2) (by norm_num) (by norm_num)
  obtain ⟨Mr, hMr, hbR⟩ := h.upper_away_left (eps := 1/2) (by norm_num) (by norm_num)
  refine ⟨max Ml Mr, hMl.trans_le (le_max_left _ _), ?_⟩
  intro x hx
  by_cases hxmid : x ≤ 1/2
  · exact (hbL x ⟨hx.1, hxmid⟩).trans (le_max_left _ _)
  · exact (hbR x ⟨(lt_of_not_ge hxmid).le, hx.2⟩).trans (le_max_right _ _)

theorem PowerProfile.global_lower_of_right_finite {f : ℝ → ℝ}
    {left : EndpointBehavior} {c : ℝ} (h : PowerProfile f left (.finite c)) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ Ioo (0 : ℝ) 1, d ≤ f x := by
  have hr := h.2.2.2.1
  have hn : ∃ d : ℝ, 0 < d ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), d ≤ f (1-s) :=
    ⟨c/2, by dsimp [RightBehavior] at hr; linarith [hr.1],
      (finite_limit_eventually_bounds hr.1 hr.2).mono fun _ hs => hs.1⟩
  obtain ⟨dr, hdr, hbR⟩ := positive_continuous_lower_from_left (continuousOn_reflect h.1)
    (positive_reflect h.2.1) hn (b := 1/2) (by norm_num) (by norm_num)
  obtain ⟨dl, hdl, hbL⟩ := h.lower_away_right (eps := 1/2) (by norm_num) (by norm_num)
  refine ⟨min dl dr, lt_min hdl hdr, ?_⟩
  intro x hx
  by_cases hxmid : x ≤ 1/2
  · exact (min_le_left _ _).trans (hbL x ⟨hx.1, by linarith⟩)
  · have hrx := hbR (1-x) ⟨by linarith [hx.2], by linarith⟩
    exact (min_le_right _ _).trans (by simpa using hrx)

/-- The full off-active-neighborhood bound stated before sp-populations.
Inactive endpoints need no cutoff. Constants may depend on the profile and eps. -/
theorem PowerProfile.bounds_off_active {f : ℝ → ℝ} {left right : EndpointBehavior}
    (h : PowerProfile f left right) {eps : ℝ} (he0 : 0 < eps) (he1 : eps < 1) :
    ∃ d M : ℝ, 0 < d ∧ 0 < M ∧ ∀ x ∈ Ioo (0 : ℝ) 1,
      (left.active → eps ≤ x) → (right.active → x ≤ 1-eps) →
      d ≤ f x ∧ f x ≤ M := by
  have hlo : ∃ d : ℝ, 0 < d ∧ ∀ x ∈ Ioo (0 : ℝ) 1,
      (right.active → x ≤ 1-eps) → d ≤ f x := by
    cases right with
    | finite c =>
      obtain ⟨d, hd, hb⟩ := h.global_lower_of_right_finite
      exact ⟨d, hd, fun x hx _ => hb x hx⟩
    | power c beta eta =>
      obtain ⟨d, hd, hb⟩ := h.lower_away_right he0 he1
      exact ⟨d, hd, fun x hx he => hb x ⟨hx.1, he trivial⟩⟩
  have hhi : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Ioo (0 : ℝ) 1,
      (left.active → eps ≤ x) → f x ≤ M := by
    cases left with
    | finite c =>
      obtain ⟨M, hM, hb⟩ := h.global_upper_of_left_finite
      exact ⟨M, hM, fun x hx _ => hb x hx⟩
    | power c alpha eta =>
      obtain ⟨M, hM, hb⟩ := h.upper_away_left he0 he1
      exact ⟨M, hM, fun x hx he => hb x ⟨he trivial, hx.2⟩⟩
  obtain ⟨d, hd, hlo⟩ := hlo
  obtain ⟨M, hM, hhi⟩ := hhi
  exact ⟨d, M, hd, hM, fun x hx hl hr => ⟨hlo x hx hr, hhi x hx hl⟩⟩

theorem PowerExpansion.exists_comparison_neighborhood {f : ℝ → ℝ} {c exponent eta : ℝ}
    (h : PowerExpansion f c exponent eta) (hc : 0 < c) (he : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ eps < 1/2 ∧ ∀ s ∈ Ioc (0 : ℝ) eps,
      (c/2)*s^exponent ≤ f s ∧ f s ≤ (3*c/2)*s^exponent := by
  obtain ⟨delta, hd, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (h.eventually_comparable hc he)
  change 0 < delta at hd
  refine ⟨min (delta/2) (1/4), lt_min (by linarith) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro s hs
  exact hb ⟨hs.1, hs.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))⟩

end Luce.Section6
