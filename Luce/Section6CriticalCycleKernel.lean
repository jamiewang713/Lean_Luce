import Luce.Section6CriticalCycleExponential

noncomputable section
open scoped BigOperators
namespace Luce.Section6

def criticalKernel (n K gamma i j : ℝ) : ℝ :=
  K/(i*Real.log (n/j))*Real.exp (-gamma*(j/(i*Real.log (n/j))))

/-- A summable maximum-root bound. The deliberately weaker power 3/2
works for every cycle length at least two. -/
theorem critical_cycle_kernel_bound {gamma : ℝ} (hg : 0 < gamma) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ n K m : ℝ, 0 < n → 0 < K → 0 < m →
      1 ≤ Real.log (n/m) → ∀ u : Fin k → ℝ, (∀ i, 0 < u i ∧ u i ≤ m) →
      (∏ a : Fin (k+1), criticalKernel n K gamma
        ((Fin.cons m u : Fin (k+1) → ℝ) a) ((Fin.snoc u m : Fin (k+1) → ℝ) a)) ≤
      (C*K^(k+1))*(Real.log (n/m))^(-(3/2 : ℝ))/m*
        ∏ i, ((1/u i)*(u i/m)^criticalCycleDecay k) := by
  obtain ⟨C,hC,hdecay⟩ := critical_log_cycle_exponential hg k
  refine ⟨C,hC,?_⟩
  intro n K m hn hK hm hz u hu
  let z := Real.log (n/m)
  let y := fun i => Real.log (m/u i)
  let s : Fin (k+1) → ℝ := Fin.cons m u
  let t : Fin (k+1) → ℝ := Fin.snoc u m
  let v : Fin (k+1) → ℝ := Fin.cons 0 y
  let v' : Fin (k+1) → ℝ := Fin.snoc y 0
  have hzp : 0 < z := by dsimp [z]; linarith
  have hu0 (i : Fin k) : 0 < u i := (hu i).1
  have huInv : 0 ≤ ∏ i, 1/u i := Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hu0 i)).le)
  have hy (i : Fin k) : 0 ≤ y i := Real.log_nonneg ((one_le_div (hu i).1).mpr (hu i).2)
  have hs (a : Fin (k+1)) : 0 < s a := by
    refine Fin.cases ?_ (fun i => ?_) a
    · exact hm
    · exact (hu i).1
  have ht (a : Fin (k+1)) : 0 < t a := by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simpa [t] using hm
    · simpa [t] using (hu i).1
  have hv (a : Fin (k+1)) : v a = Real.log (m/s a) := by
    refine Fin.cases ?_ (fun i => ?_) a
    · simp [v,s,hm.ne']
    · rfl
  have hv' (a : Fin (k+1)) : v' a = Real.log (m/t a) := by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp [v',t,hm.ne']
    · simp only [v',t,Fin.snoc_castSucc,y]
  have hv'0 (a : Fin (k+1)) : 0 ≤ v' a := by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp [v']
    · simpa [v'] using hy i
  have hlog (a : Fin (k+1)) : Real.log (n/t a) = z+v' a := by
    rw [hv']
    dsimp [z]
    rw [Real.log_div hn.ne' (ht a).ne',Real.log_div hn.ne' hm.ne',Real.log_div hm.ne' (ht a).ne']
    ring
  have hexp (a : Fin (k+1)) : Real.exp (v a-v' a) = t a/s a := by
    rw [hv,hv']
    have he : Real.log (m/s a)-Real.log (m/t a) = Real.log (t a/s a) := by
      rw [Real.log_div hm.ne' (hs a).ne',Real.log_div hm.ne' (ht a).ne',
        Real.log_div (ht a).ne' (hs a).ne']
      ring
    rw [he,Real.exp_log (div_pos (ht a) (hs a))]
  let E : Fin (k+1) → ℝ := fun a => Real.exp (-gamma*(Real.exp (v a-v' a)/(z+v' a)))
  have heq (a : Fin (k+1)) : criticalKernel n K gamma (s a) (t a) =
      (K/(s a*(z+v' a)))*E a := by
    dsimp [criticalKernel,E]
    rw [hlog,hexp,div_div]
  have hpre (a : Fin (k+1)) : K/(s a*(z+v' a)) ≤ K/(s a*z) :=
    div_le_div_of_nonneg_left hK.le (mul_pos (hs a) hzp)
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hv'0 a)) (hs a).le)
  have hprod : (∏ a, criticalKernel n K gamma (s a) (t a)) ≤
      (K/z)^(k+1)*(1/m*(∏ i, 1/u i))*(∏ a, E a) := by
    calc
      _ ≤ ∏ a, (K/(s a*z))*E a := by
        apply Finset.prod_le_prod
        · intro a _
          rw [heq]
          exact mul_nonneg (div_nonneg hK.le (mul_pos (hs a)
            (add_pos_of_pos_of_nonneg hzp (hv'0 a))).le) (Real.exp_pos _).le
        · intro a _
          rw [heq]
          exact mul_le_mul_of_nonneg_right (hpre a) (Real.exp_pos _).le
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        have hh (a : Fin (k+1)) : K/(s a*z) = (K/z)*(1/s a) := by ring
        simp_rw [hh]
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,s]
        have hc : (∏ x : Fin (k+1), 1/(Fin.cons m u : Fin (k+1) → ℝ) x) = 1/m*∏ i, 1/u i := by
          rw [Fin.prod_univ_succ]
          rfl
        rw [hc]
  have hE : (∏ a, E a) ≤ C*z^(1/2 : ℝ)*(∏ i, Real.exp (-criticalCycleDecay k*y i)) := by
    have hh := hdecay z hz y hy
    dsimp [E]
    rw [← Real.exp_sum,← Finset.mul_sum]
    exact hh
  have hepow (i : Fin k) : Real.exp (-criticalCycleDecay k*y i) = (u i/m)^criticalCycleDecay k := by
    rw [Real.rpow_def_of_pos (div_pos (hu i).1 hm)]
    congr 1
    dsimp [y]
    rw [Real.log_div hm.ne' (hu i).1.ne',Real.log_div (hu i).1.ne' hm.ne']
    ring
  simp_rw [hepow] at hE
  have hzpow : z^(1/2 : ℝ)/z^(k+1) ≤ z^(-(3/2 : ℝ)) := by
    calc
      _ ≤ z^(1/2 : ℝ)/z^2 := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hz (by omega))
      _ = _ := by
        rw [← Real.rpow_natCast z 2,← Real.rpow_sub hzp]
        congr 1
        norm_num
  have hh := hprod.trans (mul_le_mul_of_nonneg_left hE (by positivity))
  have hid : (K/z)^(k+1)*(1/m*(∏ i, 1/u i))*(C*z^(1/2 : ℝ)*∏ i, (u i/m)^criticalCycleDecay k) =
      (C*K^(k+1)/m)*(z^(1/2 : ℝ)/z^(k+1))*∏ i, ((1/u i)*(u i/m)^criticalCycleDecay k) := by
    rw [Finset.prod_mul_distrib,div_pow]
    ring
  rw [hid] at hh
  exact hh.trans (by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzpow (by positivity : 0 ≤ C*K^(k+1)/m))
      (show 0 ≤ ∏ i, ((1/u i)*(u i/m)^criticalCycleDecay k) from Finset.prod_nonneg (fun i _ =>
        mul_nonneg (one_div_pos.mpr (hu0 i)).le (Real.rpow_nonneg (div_pos (hu0 i) hm).le _)))
    convert h using 1 <;> ring)

end Luce.Section6
