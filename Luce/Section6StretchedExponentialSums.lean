import Luce.Section6EnvelopeAbsorption
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section
open Filter
open scoped Topology
namespace Luce.Section6

/-- Polynomially weighted stretched exponentials are summable. The zero
term is harmless; the comparison with the p-series is only eventual. -/
theorem summable_weighted_stretched_exp {b d nu : ℝ} (hb : 0 ≤ b)
    (hd : 0 < d) (hnu : 0 < nu) :
    Summable (fun n : ℕ => (n : ℝ)^b*Real.exp (-d*(n : ℝ)^nu)) := by
  obtain ⟨C, hC, habs⟩ := power_envelope_absorption (a := b+2) hnu.ne'
    (div_nonneg (by linarith) hnu.le)
  let K := C*(1/(d/2))^((b+2)/nu)
  have hK : 0 < K := by dsimp [K]; positivity
  apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hbound : (n : ℝ)^(b+2)*Real.exp (-d*(n : ℝ)^nu) ≤ K := by
    have hh := habs d (n : ℝ) hd hnR
    have he : Real.exp (-((d/2)*(n : ℝ)^nu)) ≤ 1 := Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg (half_pos hd).le (Real.rpow_nonneg hnR.le nu)))
    have hh' := hh.trans (mul_le_mul_of_nonneg_left he hK.le)
    simpa only [mul_one, neg_mul] using hh'
  have he : (n : ℝ)^b*Real.exp (-d*(n : ℝ)^nu) =
      ((n : ℝ)^(b+2)*Real.exp (-d*(n : ℝ)^nu))*(n : ℝ)^(-2 : ℝ) := by
    rw [mul_right_comm, ← Real.rpow_add hnR]
    congr 2
    ring
  simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hnR.le b) (Real.exp_pos _).le),
    abs_of_nonneg (Real.rpow_nonneg hnR.le (-2))]
  rw [he]
  exact mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hnR.le _)

/-- A uniform stretched-exponential tail bound for weighted series, with
half the decay retained. No summability hypothesis is passed by callers. -/
theorem weighted_stretched_exp_tail {b d nu : ℝ} (hb : 0 ≤ b)
    (hd : 0 < d) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ,
      (∑' n : ℕ, if A ≤ n then (n : ℝ)^b*Real.exp (-d*(n : ℝ)^nu) else 0) ≤
        C*Real.exp (-(d/2)*(A : ℝ)^nu) := by
  have hs := summable_weighted_stretched_exp hb (half_pos hd) hnu
  let S := ∑' n : ℕ, (n : ℝ)^b*Real.exp (-(d/2)*(n : ℝ)^nu)
  refine ⟨max 1 S, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro A
  have hpoint (n : ℕ) :
      (if A ≤ n then (n : ℝ)^b*Real.exp (-d*(n : ℝ)^nu) else 0) ≤
      Real.exp (-(d/2)*(A : ℝ)^nu)*((n : ℝ)^b*Real.exp (-(d/2)*(n : ℝ)^nu)) := by
    split_ifs with hn
    · have hp := Real.rpow_le_rpow (Nat.cast_nonneg A) (Nat.cast_le.mpr hn) hnu.le
      have hex : Real.exp (-(d/2)*(n : ℝ)^nu) ≤ Real.exp (-(d/2)*(A : ℝ)^nu) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have he : Real.exp (-d*(n : ℝ)^nu) =
          Real.exp (-(d/2)*(n : ℝ)^nu)*Real.exp (-(d/2)*(n : ℝ)^nu) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_right hex
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) b) (Real.exp_pos (-(d/2)*(n : ℝ)^nu)).le)]
    · positivity
  have hnonneg (n : ℕ) : 0 ≤ (if A ≤ n then (n : ℝ)^b*Real.exp (-d*(n : ℝ)^nu) else 0) := by
    split_ifs <;> positivity
  have hsum := Summable.of_nonneg_of_le hnonneg hpoint (hs.mul_left _)
  calc
    _ ≤ ∑' n : ℕ, Real.exp (-(d/2)*(A : ℝ)^nu)*((n : ℝ)^b*Real.exp (-(d/2)*(n : ℝ)^nu)) :=
      hsum.tsum_le_tsum hpoint (hs.mul_left _)
    _ = Real.exp (-(d/2)*(A : ℝ)^nu)*S := by rw [tsum_mul_left]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) S)
        (Real.exp_pos (-(d/2)*(A : ℝ)^nu)).le
      nlinarith

end Luce.Section6
