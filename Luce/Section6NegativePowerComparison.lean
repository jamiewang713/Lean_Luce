import Luce.Section6NegativePowerInversion

noncomputable section
open Set
namespace Luce.Section6

/-- Two populations with the same power scale can be compared at the
exact quantile of the first one. Smallness is discharged by the concrete
quantile-control argument before applying this helper. -/
theorem negative_power_weighted_comparison {A B p q K L : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q)
    (hK : 0 < K) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ N x t z : ℝ, 0 < N → 0 < x → 0 < t →
      |x-A*t^(-p)| ≤ K*(t^(-(p+q))+1/N) →
      |z-B*t^(-p)| ≤ L*(t^(-(p+q))+1/N) →
      K*t^(-q) ≤ A/4 → K/N ≤ x/4 →
      |z/(B*x/A)-1| ≤ C*(x^(q/p)+1/(N*x)) := by
  let E := A*L/B+K
  let Q := (2/A)*(2/A)^(q/p)
  have hE : 0 < E := by dsimp [E]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨E*(Q+1), by positivity, ?_⟩
  intro N x t z hN hx ht herr hz hsmall hdisc
  let y := A*t^(-p)
  have hy : 0 < y := mul_pos hA (Real.rpow_pos_of_pos ht _)
  have hprod : t^(-(p+q)) = t^(-p)*t^(-q) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have herr' : |x-y| ≤ y/4+x/4 := by
    have hs := mul_le_mul_of_nonneg_left hsmall (Real.rpow_pos_of_pos ht (-p)).le
    rw [hprod] at herr
    calc
      _ ≤ K*(t^(-p)*t^(-q)+1/N) := herr
      _ = t^(-p)*(K*t^(-q))+K/N := by ring
      _ ≤ t^(-p)*(A/4)+x/4 := add_le_add hs hdisc
      _ = _ := by dsimp [y]; ring
  have hratio : y/x ∈ Icc (1/2 : ℝ) 2 := by
    have hh := abs_le.mp herr'
    constructor
    · apply (le_div_iff₀ hx).mpr
      linarith [hh.1, hh.2]
    · apply (div_le_iff₀ hx).mpr
      linarith [hh.1, hh.2]
  have htbase : t^(-p) ≤ 2*x/A := by
    have hh := (div_le_iff₀ hx).mp hratio.2
    apply (le_div_iff₀ hA).mpr
    dsimp [y] at hh
    nlinarith
  have htq : t^(-q) ≤ (2/A)^(q/p)*x^(q/p) := by
    have hh := Real.rpow_le_rpow (Real.rpow_pos_of_pos ht (-p)).le htbase (div_pos hq hp).le
    rw [← Real.rpow_mul ht.le, show (-p)*(q/p) = -q by field_simp] at hh
    rw [show 2*x/A = (2/A)*x by ring, Real.mul_rpow (by positivity) hx.le] at hh
    exact hh
  have hbaseNorm : t^(-p)/x ≤ 2/A := by
    apply (div_le_iff₀ hx).mpr
    exact htbase.trans_eq (by ring)
  have hmul := mul_le_mul hbaseNorm htq (Real.rpow_pos_of_pos ht (-q)).le (by positivity : 0 ≤ 2/A)
  have hF : (t^(-(p+q))+1/N)/x ≤ Q*x^(q/p)+1/(N*x) := by
    calc
      _ = (t^(-p)/x)*t^(-q)+1/(N*x) := by rw [hprod]; field_simp
      _ ≤ (2/A)*((2/A)^(q/p)*x^(q/p))+1/(N*x) := add_le_add hmul (le_refl _)
      _ = _ := by dsimp [Q]; ring
  have hcomp : |z-(B/A)*x| ≤ (L+(B/A)*K)*(t^(-(p+q))+1/N) := by
    have hid : B*t^(-p)-(B/A)*x = (B/A)*(A*t^(-p)-x) := by field_simp
    calc
      _ ≤ |z-B*t^(-p)|+|B*t^(-p)-(B/A)*x| := abs_sub_le _ _ _
      _ = |z-B*t^(-p)|+(B/A)*|x-A*t^(-p)| := by
        rw [hid, abs_mul, abs_of_pos (div_pos hB hA), abs_sub_comm (A*t^(-p)) x]
      _ ≤ L*(t^(-(p+q))+1/N)+(B/A)*(K*(t^(-(p+q))+1/N)) :=
        add_le_add hz (mul_le_mul_of_nonneg_left herr (div_pos hB hA).le)
      _ = _ := by ring
  have he : |z/(B*x/A)-1| ≤ E*((t^(-(p+q))+1/N)/x) := by
    have hden : 0 < B*x/A := by positivity
    rw [div_sub_one hden.ne', abs_div, abs_of_pos hden]
    have hh := div_le_div_of_nonneg_right hcomp hden.le
    rw [show (B/A)*x = B*x/A by ring] at hh
    exact hh.trans_eq (by dsimp [E]; field_simp)
  have hsum : Q*x^(q/p)+1/(N*x) ≤ (Q+1)*(x^(q/p)+1/(N*x)) := by
    have h1 := mul_nonneg hQ.le (by positivity : 0 ≤ 1/(N*x))
    have h2 := (Real.rpow_pos_of_pos hx (q/p)).le
    nlinarith
  exact he.trans ((mul_le_mul_of_nonneg_left (hF.trans hsum) hE.le).trans_eq (by ring))

end Luce.Section6
