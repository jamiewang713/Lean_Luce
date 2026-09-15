import Luce.Section6IdealCoreGrowth

noncomputable section
open Filter
namespace Luce.Section6

/-- Exact cutoff information needed to subtract two total traces. -/
structure IdealSpatialWindow68 (n : ℕ) (a b c : ℝ) : Prop where
  n_pos : 1 ≤ n
  lower_le : idealCoreLower n ≤ ⌊(n : ℝ)^a⌋₊
  threshold_le : ⌊(n : ℝ)^a⌋₊ ≤ ⌊(n : ℝ)^b⌋₊
  upper_le : ⌊(n : ℝ)^b⌋₊+1 ≤ idealCoreUpper n
  core_le_n : idealCoreUpper n ≤ n
  floor_a_error : |Real.log (⌊(n : ℝ)^a⌋₊ : ℝ)-a*Real.log (n : ℝ)| ≤ 1/(idealCoreLower n : ℝ)
  floor_b_error : |Real.log (⌊(n : ℝ)^b⌋₊ : ℝ)-b*Real.log (n : ℝ)| ≤ 1/(idealCoreLower n : ℝ)
  succ_a_error : |Real.log ((⌊(n : ℝ)^a⌋₊+1 : ℕ) : ℝ)-a*Real.log (n : ℝ)| ≤ 1/(idealCoreLower n : ℝ)
  succ_b_error : |Real.log ((⌊(n : ℝ)^b⌋₊+1 : ℕ) : ℝ)-b*Real.log (n : ℝ)| ≤ 1/(idealCoreLower n : ℝ)
  left_gap : Real.log (idealCoreLower n : ℝ) ≤
    c*Real.log ((⌊(n : ℝ)^a⌋₊ : ℝ)/(idealCoreLower n : ℝ))
  right_gap : Real.log (idealCoreLower n : ℝ) ≤
    c*Real.log ((idealCoreUpper n : ℝ)/((⌊(n : ℝ)^b⌋₊+1 : ℕ) : ℝ))

theorem idealSpatialWindow68_eventually {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, IdealSpatialWindow68 n a b c := by
  let e := min (1/4 : ℝ) (min (a/4) (min ((1-b)/4) (min (c*a/4) (c*(1-b)/4))))
  have he : 0 < e := by dsimp [e]; positivity
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [idealCoreLower_log_sublinear68 he, eventually_ge_atTop 1,
    hlog.eventually_ge_atTop (8/a), hlog.eventually_ge_atTop (8/(1-b)),
    hlog.eventually_ge_atTop 4] with n hsmall hn hlargeA hlargeB hlarge
  let A := idealCoreLower n
  let B := idealCoreUpper n
  let P := ⌊(n : ℝ)^a⌋₊
  let Q := ⌊(n : ℝ)^b⌋₊
  let L := Real.log (n : ℝ)
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hAone : 1 ≤ A := idealCoreLower_pos68 n
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hAL : Real.log (A : ℝ) ≤ L/4 := by
    have he1 : e ≤ 1/4 := min_le_left _ _
    have := mul_le_mul_of_nonneg_right he1 hL
    dsimp only [A,L] at *
    linarith
  have hAa : Real.log (A : ℝ) ≤ a*L/4 := by
    have he1 : e ≤ a/4 := (min_le_right _ _).trans (min_le_left _ _)
    have := mul_le_mul_of_nonneg_right he1 hL
    linarith
  have hAb : Real.log (A : ℝ) ≤ (1-b)*L/4 := by
    have he1 : e ≤ (1-b)/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have := mul_le_mul_of_nonneg_right he1 hL
    linarith
  have hAca : Real.log (A : ℝ) ≤ c*(a*L)/4 := by
    have he1 : e ≤ c*a/4 := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have := mul_le_mul_of_nonneg_right he1 hL
    nlinarith only [hsmall, this]
  have hAcb : Real.log (A : ℝ) ≤ c*((1-b)*L)/4 := by
    have he1 : e ≤ c*(1-b)/4 := (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have := mul_le_mul_of_nonneg_right he1 hL
    nlinarith only [hsmall, this]
  have hla : 8 ≤ a*L := by have := (div_le_iff₀ ha).mp hlargeA; nlinarith
  have hlb : 8 ≤ (1-b)*L := by have := (div_le_iff₀ (sub_pos.mpr hb)).mp hlargeB; nlinarith
  have hAn : (A : ℝ) ≤ n := (Real.log_le_log_iff hA0 hn0).mp (by change _ ≤ L; linarith)
  have hdiv : 1 ≤ (n : ℝ)/A := (one_le_div hA0).mpr hAn
  have hBpos : 0 < B := Nat.floor_pos.mpr hdiv
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hBerr := (log_floor_errors_le_one68 hdiv).1
  change |Real.log (B : ℝ)-Real.log ((n : ℝ)/A)| ≤ 1 at hBerr
  rw [Real.log_div hn0.ne' hA0.ne'] at hBerr
  have hBlog : L-Real.log (A : ℝ)-1 ≤ Real.log (B : ℝ) := by
    have := (abs_le.mp hBerr).1
    linarith
  have hBn : B ≤ n := by
    have hfloor := Nat.floor_le (show (0 : ℝ) ≤ n/A by positivity)
    have hdivn : (n : ℝ)/A ≤ n := div_le_self hn0.le (by exact_mod_cast hAone)
    exact_mod_cast hfloor.trans hdivn
  have hpa : 1 ≤ (n : ℝ)^a := Real.one_le_rpow hnR ha.le
  have hpb : 1 ≤ (n : ℝ)^b := Real.one_le_rpow hnR (ha.trans hab).le
  have hPpos : 0 < P := Nat.floor_pos.mpr hpa
  have hQpos : 0 < Q := Nat.floor_pos.mpr hpb
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hQ10 : (0 : ℝ) < (Q+1 : ℕ) := by positivity
  have hPe := log_floor_errors_le_one68 hpa
  have hQe := log_floor_errors_le_one68 hpb
  rw [Real.log_rpow hn0] at hPe hQe
  have hPlog : a*L-1 ≤ Real.log (P : ℝ) := by have := (abs_le.mp hPe.1).1; linarith
  have hQlog : Real.log ((Q+1 : ℕ) : ℝ) ≤ b*L+1 := by have := (abs_le.mp hQe.2).2; linarith
  have hleft : a*L/2 ≤ Real.log (P : ℝ)-Real.log (A : ℝ) := by linarith
  have hright : (1-b)*L/2 ≤ Real.log (B : ℝ)-Real.log ((Q+1 : ℕ) : ℝ) := by linarith
  have hAP : A ≤ P := by
    have h := (Real.log_le_log_iff hA0 hP0).mp (by linarith)
    exact_mod_cast h
  have hPQ : P ≤ Q := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hnR hab.le)
  have hQB : Q+1 ≤ B := by
    have h := (Real.log_le_log_iff hQ10 hB0).mp (by linarith)
    exact_mod_cast h
  have hPe' := log_floor_errors68 hpa
  have hQe' := log_floor_errors68 hpb
  rw [Real.log_rpow hn0] at hPe' hQe'
  have hPA : 1/(P : ℝ) ≤ 1/(A : ℝ) := one_div_le_one_div_of_le hA0 (by exact_mod_cast hAP)
  have hQA : 1/(Q : ℝ) ≤ 1/(A : ℝ) := one_div_le_one_div_of_le hA0 (by exact_mod_cast hAP.trans hPQ)
  refine ⟨hn,hAP,hPQ,hQB,hBn,hPe'.1.trans hPA,hQe'.1.trans hQA,
    hPe'.2.trans hPA,hQe'.2.trans hQA,?_,?_⟩
  · change Real.log (A : ℝ) ≤ c*Real.log ((P : ℝ)/A)
    rw [Real.log_div hP0.ne' hA0.ne']
    have := mul_le_mul_of_nonneg_left hleft hc.le
    have hpos : 0 ≤ c*(a*L) := mul_nonneg hc.le (by linarith only [hla])
    nlinarith only [hAca, this, hpos]
  · change Real.log (A : ℝ) ≤ c*Real.log ((B : ℝ)/(Q+1 : ℕ))
    rw [Real.log_div hB0.ne' hQ10.ne']
    have := mul_le_mul_of_nonneg_left hright hc.le
    have hpos : 0 ≤ c*((1-b)*L) := mul_nonneg hc.le (by linarith only [hlb])
    nlinarith only [hAcb, this, hpos]

end Luce.Section6
