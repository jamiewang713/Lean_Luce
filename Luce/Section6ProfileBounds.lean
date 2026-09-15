import Luce.Section6EndpointBounds
import Mathlib.Topology.Order.Compact

noncomputable section
open Set Filter
open scoped Topology
namespace Luce.Section6

theorem positive_continuous_compact_bounds {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo 0 1)) (hp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ∃ d M : ℝ, 0 < d ∧ 0 < M ∧ ∀ x ∈ Icc a b, d ≤ f x ∧ f x ≤ M := by
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) (hf.mono hsub)
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) (hf.mono hsub)
  exact ⟨f u, f v, hp _ (hsub hu), hp _ (hsub hv), fun x hx => ⟨hmin hx, hmax hx⟩⟩

theorem finite_limit_eventually_bounds {g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : Tendsto g (𝓝[>] 0) (𝓝 c)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), c/2 ≤ g s ∧ g s ≤ 2*c := by
  have he := h.eventually (Ioo_mem_nhds (by linarith : c/2 < c) (by linarith : c < 2*c))
  exact he.mono fun _ hs => ⟨hs.1.le, hs.2.le⟩

/-- Every permitted left endpoint has a positive local lower bound, even
when its rates diverge. This does not bound the active right endpoint. -/
theorem LeftBehavior.eventually_lower {f : ℝ → ℝ} {left : EndpointBehavior}
    (h : LeftBehavior f left) : ∃ d : ℝ, 0 < d ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), d ≤ f s := by
  cases left with
  | finite c =>
    exact ⟨c/2, by dsimp [LeftBehavior] at h; linarith [h.1],
      (finite_limit_eventually_bounds h.1 h.2).mono fun _ hs => hs.1⟩
  | power c alpha eta =>
    rcases h with ⟨hc, ha, he, hex⟩
    refine ⟨c/2, by positivity, ?_⟩
    filter_upwards [hex.eventually_comparable hc he, self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with s hs hs0 hs1
    have hr := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 hs1.le
      (by linarith : -alpha ≤ 0)
    exact (le_mul_of_one_le_right (by positivity : 0 ≤ c/2) hr).trans hs.1

/-- Every permitted right endpoint has a finite local upper bound. -/
theorem RightBehavior.eventually_upper {f : ℝ → ℝ} {right : EndpointBehavior}
    (h : RightBehavior f right) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), f (1-s) ≤ M := by
  cases right with
  | finite c =>
    exact ⟨2*c, by dsimp [RightBehavior] at h; linarith [h.1],
      (finite_limit_eventually_bounds h.1 h.2).mono fun _ hs => hs.2⟩
  | power c beta eta =>
    rcases h with ⟨hc, hb, he, hex⟩
    refine ⟨3*c/2, by positivity, ?_⟩
    filter_upwards [hex.eventually_comparable hc he, self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with s hs hs0 hs1
    have hr := Real.rpow_le_one hs0.le hs1.le hb.le
    exact hs.2.trans (mul_le_of_le_one_right (by positivity) hr)

theorem positive_continuous_lower_from_left {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo 0 1)) (hp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x)
    (he : ∃ d : ℝ, 0 < d ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), d ≤ f s)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ Ioc (0 : ℝ) b, d ≤ f x := by
  obtain ⟨d, hd, he⟩ := he
  obtain ⟨delta, hdelta, hnear⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  change 0 < delta at hdelta
  let a := min (delta/2) (b/2)
  have ha : 0 < a := lt_min (by linarith) (by linarith)
  have hab : a ≤ b := (min_le_right _ _).trans (by linarith)
  have had : a < delta := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨dm, M, hdm, _, hmid⟩ := positive_continuous_compact_bounds hf hp ha hb1 hab
  refine ⟨min d dm, lt_min hd hdm, ?_⟩
  intro x hx
  by_cases hxa : x < a
  · exact (min_le_left _ _).trans (hnear ⟨hx.1, hxa.trans had⟩)
  · exact (min_le_right _ _).trans (hmid x ⟨le_of_not_gt hxa, hx.2⟩).1

theorem positive_continuous_upper_from_left {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo 0 1)) (hp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x)
    (he : ∃ M : ℝ, 0 < M ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), f s ≤ M)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Ioc (0 : ℝ) b, f x ≤ M := by
  obtain ⟨M, hM, he⟩ := he
  obtain ⟨delta, hdelta, hnear⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  change 0 < delta at hdelta
  let a := min (delta/2) (b/2)
  have ha : 0 < a := lt_min (by linarith) (by linarith)
  have hab : a ≤ b := (min_le_right _ _).trans (by linarith)
  have had : a < delta := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨d, Mm, _, hMm, hmid⟩ := positive_continuous_compact_bounds hf hp ha hb1 hab
  refine ⟨max M Mm, hM.trans_le (le_max_left _ _), ?_⟩
  intro x hx
  by_cases hxa : x < a
  · exact (hnear ⟨hx.1, hxa.trans had⟩).trans (le_max_left _ _)
  · exact (hmid x ⟨le_of_not_gt hxa, hx.2⟩).2.trans (le_max_right _ _)

theorem continuousOn_reflect {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo 0 1)) :
    ContinuousOn (fun x => f (1-x)) (Ioo (0 : ℝ) 1) := by
  apply hf.comp (continuous_const.sub continuous_id).continuousOn
  intro x hx
  change 1-x ∈ Ioo (0 : ℝ) 1
  constructor <;> linarith [hx.1, hx.2]

theorem positive_reflect {f : ℝ → ℝ} (hp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < f x) :
    ∀ x ∈ Ioo (0 : ℝ) 1, 0 < f (1-x) := by
  intro x hx
  apply hp
  constructor <;> linarith [hx.1, hx.2]

theorem PowerProfile.lower_away_right {f : ℝ → ℝ} {left right : EndpointBehavior}
    (h : PowerProfile f left right) {eps : ℝ} (he0 : 0 < eps) (he1 : eps < 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ Ioc (0 : ℝ) (1-eps), d ≤ f x :=
  positive_continuous_lower_from_left h.1 h.2.1 h.2.2.1.eventually_lower
    (by linarith) (by linarith)

theorem PowerProfile.upper_away_left {f : ℝ → ℝ} {left right : EndpointBehavior}
    (h : PowerProfile f left right) {eps : ℝ} (he0 : 0 < eps) (he1 : eps < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Ico eps (1 : ℝ), f x ≤ M := by
  obtain ⟨M, hM, hb⟩ := positive_continuous_upper_from_left (continuousOn_reflect h.1)
    (positive_reflect h.2.1) h.2.2.2.1.eventually_upper
    (b := 1-eps) (by linarith) (by linarith)
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hs := hb (1-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  simpa using hs

end Luce.Section6
