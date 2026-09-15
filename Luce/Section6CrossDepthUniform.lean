import Luce.Section6CrossDepthAlgebra

noncomputable section
namespace Luce.Section6

/-- Assemble three uniform one-depth estimates into the off-diagonal
time and hazard estimates. Every input is a deterministic estimate; the
profile-specific applications below discharge these inputs. -/
theorem cross_depth_uniform_transport
    (depth : ∀ n, Fin n → ℕ) (rate time weight : ∀ n, Fin n → ℝ)
    (hdepth : ∀ n i, 0 < depth n i) (hrate : ∀ n i, 0 < rate n i)
    {c p gamma q eta xr xh R T H dr dt dh Mt Mh : ℝ}
    (hc : 0 < c) (hg : 0 < gamma) (hq : 0 < q)
    (heta : 0 < eta) (hxr : 0 < xr) (hxh : 0 < xh)
    (hR : 0 < R) (hT : 0 < T) (hH : 0 < H)
    (hdr : 0 < dr) (hdt : 0 < dt) (hdh : 0 < dh)
    (hr : ∀ n (i : Fin n), (depth n i : ℝ)/(n : ℝ) < dr →
      |rate n i/(c*((depth n i : ℝ)/(n : ℝ))^p)-1| ≤
        R*(((depth n i : ℝ)/(n : ℝ))^eta+1/(depth n i : ℝ)))
    (ht : ∀ n (i : Fin n), Mt ≤ (depth n i : ℝ) → (depth n i : ℝ)/(n : ℝ) < dt →
      |rate n i*time n i/q-1| ≤ T*(((depth n i : ℝ)/(n : ℝ))^xr+1/(depth n i : ℝ)))
    (hw : ∀ n (i : Fin n), Mh ≤ (depth n i : ℝ) → (depth n i : ℝ)/(n : ℝ) < dh →
      |(rate n i/weight n i)/(gamma*q/(depth n i : ℝ))-1| ≤
        H*(((depth n i : ℝ)/(n : ℝ))^xh+1/(depth n i : ℝ))) :
    ∃ rho C delta M : ℝ, 0 < rho ∧ 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧ 1 ≤ M ∧
      ∀ n (i j : Fin n), M ≤ (depth n i : ℝ) → M ≤ (depth n j : ℝ) →
        (depth n i : ℝ)/(n : ℝ) < delta → (depth n j : ℝ)/(n : ℝ) < delta →
        let x := ((depth n i : ℝ)/(depth n j : ℝ))^p
        let e := crossDepthError rho n (depth n i) (depth n j)
        |rate n i*time n j/(q*x)-1| ≤ C*e ∧
        |(rate n i/weight n j)/(gamma*q*x/(depth n j : ℝ))-1| ≤ C*e := by
  let rho := min eta (min xr xh)
  have hrho : 0 < rho := lt_min heta (lt_min hxr hxh)
  obtain ⟨ds, Ms, hds, _, hsmall⟩ := joint_power_error_small hrho hR (by norm_num : (0 : ℝ) < 1/2)
  let delta := min 1 (min dr (min dt (min dh ds)))
  let M := max 1 (max Mt (max Mh Ms))
  refine ⟨rho, 8*R*(T+H)+4*R+(T+H), delta, M, hrho, by positivity,
    lt_min zero_lt_one (lt_min hdr (lt_min hdt (lt_min hdh hds))), min_le_left _ _, le_max_left _ _, ?_⟩
  intro n i j hi hj his hjs
  dsimp only
  let a : ℝ := depth n i
  let h : ℝ := depth n j
  let e := crossDepthError rho n a h
  have ha : 0 < a := Nat.cast_pos.mpr (hdepth n i)
  have hh : 0 < h := Nat.cast_pos.mpr (hdepth n j)
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have ha1 : 1 ≤ a := (le_max_left _ _).trans hi
  have hh1 : 1 ≤ h := (le_max_left _ _).trans hj
  have hx : 0 < max a h/(n : ℝ) := div_pos (ha.trans_le (le_max_left _ _)) hn
  have hxs : max a h/(n : ℝ) < delta := by
    rw [← max_div_div_right hn.le]
    exact max_lt his hjs
  have hx1 : max a h/(n : ℝ) ≤ 1 := hxs.le.trans (min_le_left _ _)
  have hds' : max a h/(n : ℝ) < ds :=
    (((hxs.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)).trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hm : Ms ≤ min a h := by
    have hMs : Ms ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    exact le_min (hMs.trans hi) (hMs.trans hj)
  have he := crossDepthError_nonneg (rho := rho) hn ha hh
  have he2 := crossDepthError_le_two hn ha1 hh1 hrho.le hx1
  have hsmall' : R*e ≤ 1/2 := hsmall _ _ hx hds' hm
  have hcutr : delta ≤ dr := (min_le_right _ _).trans (min_le_left _ _)
  have hcutt : delta ≤ dt := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcutw : delta ≤ dh := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hleft : ∀ z, rho ≤ z → (a/(n : ℝ))^z+1/a ≤ e := fun z hz =>
    one_depth_error_le_cross hn ha hh hrho.le hz hx1
  have hright : ∀ z, rho ≤ z → (h/(n : ℝ))^z+1/h ≤ e := by
    intro z hz
    simpa only [e, crossDepthError, max_comm h a, min_comm h a] using
      one_depth_error_le_cross hn hh ha hrho.le hz (by simpa only [max_comm h a] using hx1)
  have hra := (hr n i (his.trans_le hcutr)).trans
    (mul_le_mul_of_nonneg_left (hleft eta (min_le_left _ _)) hR.le)
  have hrb := (hr n j (hjs.trans_le hcutr)).trans
    (mul_le_mul_of_nonneg_left (hright eta (min_le_left _ _)) hR.le)
  have hMt : Mt ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMh : Mh ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have htime := (ht n j (hMt.trans hj) (hjs.trans_le hcutt)).trans
    (mul_le_mul_of_nonneg_left (hright xr ((min_le_right _ _).trans (min_le_left _ _))) hT.le)
  have hweight := (hw n j (hMh.trans hj) (hjs.trans_le hcutw)).trans
    (mul_le_mul_of_nonneg_left (hright xh ((min_le_right _ _).trans (min_le_right _ _))) hH.le)
  have htime' : |rate n j*time n j/q-1| ≤ (T+H)*e := htime.trans (by
    exact mul_le_mul_of_nonneg_right (by linarith) he)
  have hweight' : |(rate n j/weight n j)/(gamma*q/h)-1| ≤ (T+H)*e := hweight.trans (by
    exact mul_le_mul_of_nonneg_right (by linarith) he)
  have hA : 0 < c*(a/(n : ℝ))^p := by positivity
  have hB : 0 < c*(h/(n : ℝ))^p := by positivity
  have ht' := cross_depth_relative_transport (hrate n j) hA hB hq hR.le (by positivity : 0 ≤ T+H)
    he he2 hra hrb hsmall' htime'
  have hw' := cross_depth_relative_transport (v := 1/weight n j) (hrate n j) hA hB
    (by positivity : 0 < gamma*q/h) hR.le (by positivity : 0 ≤ T+H)
    he he2 hra hrb hsmall' (by simpa only [mul_one_div] using hweight')
  rw [sampled_power_ratio hc hn ha hh] at ht' hw'
  constructor
  · simpa only [mul_comm q] using ht'
  · convert hw' using 1 <;> dsimp only [a, h, e] <;> congr 2 <;> ring

end Luce.Section6
