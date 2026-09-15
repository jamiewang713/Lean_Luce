import Luce.Section6ExceptionalSums

noncomputable section
namespace Luce.Section6

/-- Stretched exponential decay implies an inverse-depth bound, with its
constant derived from the already proved summability theorem. -/
theorem stretched_exp_le_inverse_depth {d nu : ℝ} (hd : 0 < d) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 1 ≤ h → Real.exp (-d*(h : ℝ)^nu) ≤ C/(h : ℝ) := by
  have hs : Summable (fun h : ℕ => (h : ℝ)*Real.exp (-d*(h : ℝ)^nu)) := by
    simpa only [Real.rpow_one] using summable_weighted_stretched_exp (b := 1) zero_le_one hd hnu
  let C : ℝ := max 1 (∑' h : ℕ, (h : ℝ)*Real.exp (-d*(h : ℝ)^nu))
  refine ⟨C, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro h hh
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  apply (le_div_iff₀ hhR).mpr
  have he := (hs.le_tsum h (fun k _ => by positivity)).trans (le_max_right 1 _)
  simpa only [C, mul_comm] using he

/-- Both literal exceptional envelopes obey the target inverse-depth bound.
The right case uses its proved support h<a; the left is its transpose. -/
theorem exceptionalEnvelope_target_bound {b v d nu : ℝ}
    (hb : 0 < b) (hv : 0 < v) (hd : 0 < d) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ a h : ℕ, 1 ≤ a → 1 ≤ h →
      exceptionalEnvelope b v d nu a h ≤ C/(h : ℝ) ∧
      exceptionalEnvelope b v d nu h a ≤ C/(h : ℝ) := by
  obtain ⟨C, hC, hc⟩ := stretched_exp_le_inverse_depth hd hnu
  refine ⟨C, hC, ?_⟩
  intro a h ha hh
  constructor
  · by_cases hz : exceptionalEnvelope b v d nu a h = 0
    · rw [hz]; positivity
    · have hha := (exceptionalEnvelope_support hb hv ha hh hz).le
      have hhaR : (h : ℝ) ≤ a := by exact_mod_cast hha
      have he : Real.exp (-d*(a : ℝ)^nu) ≤ Real.exp (-d*(h : ℝ)^nu) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left (Real.rpow_le_rpow (Nat.cast_nonneg h) hhaR hnu.le)
          (neg_nonpos.mpr hd.le)
      exact (exceptionalEnvelope_le_exp b v d nu a h).trans (he.trans (hc h hh))
  · exact (exceptionalEnvelope_le_exp b v d nu h a).trans (hc h hh)

/-- Ordinary plus exceptional comparison kernels have inverse target-depth
maxima. No bound on the ordinary kernel argument is needed. -/
theorem endpoint_envelope_target_bound {b v d nu : ℝ}
    (hb : 0 < b) (hv : 0 < v) (hd : 0 < d) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a h : ℕ) (x : ℝ), 1 ≤ a → 1 ≤ h →
      (x/(h : ℝ))*Real.exp (-d*x)+exceptionalEnvelope b v d nu a h ≤ C/(h : ℝ) ∧
      (x/(h : ℝ))*Real.exp (-d*x)+exceptionalEnvelope b v d nu h a ≤ C/(h : ℝ) := by
  obtain ⟨B, hB, hbnd⟩ := exceptionalEnvelope_target_bound hb hv hd hnu
  refine ⟨Real.exp (-1)/d+B, add_pos (by positivity) hB, ?_⟩
  intro a h x ha hh
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr (by omega)
  have hx : x*Real.exp (-d*x) ≤ Real.exp (-1)/d := by
    simpa [rateKernel, survivalKernel] using rateKernel_le_exp_neg_one_div (a := x) hd
  have ho : (x/(h : ℝ))*Real.exp (-d*x) ≤ (Real.exp (-1)/d)/(h : ℝ) := by
    simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hx hhR.le
  constructor
  · exact (add_le_add ho (hbnd a h ha hh).1).trans_eq (add_div _ _ _).symm
  · exact (add_le_add ho (hbnd a h ha hh).2).trans_eq (add_div _ _ _).symm

end Luce.Section6
