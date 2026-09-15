import Luce.Section6CriticalCycleProbability

noncomputable section
open MeasureTheory Function
open scoped BigOperators
namespace Luce.Section6

theorem CriticalProfile.critical_root_probability {f : ℝ → ℝ} {c eta d : ℝ}
    (hp : CriticalProfile f c eta d) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C Z : ℝ, 0 < C ∧ 2 ≤ Z ∧
      ∀ (grid : SamplingGrid) (w : WeightArray), SampledRates grid w f →
      ∀ n M B : ℕ, 8*(k+1)+8 ≤ M → 8*B ≤ n →
      Z ≤ Real.log (n : ℝ)-Real.log (B : ℝ) →
      ∀ v ∈ criticalBlock n M B,
      (exponentialRace (w n)).real (retainedMaximumCycleEvent k (criticalBlock n M B) v) ≤
        C*(Real.log ((n : ℝ)/((v.val : ℝ)+1)))^(-(3/2 : ℝ))/((v.val : ℝ)+1) := by
  classical
  obtain ⟨K,gamma,Z,hK,hgamma,hZ,hmat⟩ := hp.critical_domination_matrix (k+1) (by omega)
  obtain ⟨C,hC,hcycle⟩ := critical_cycle_kernel_bound hgamma k hk
  let a := criticalCycleDecay k
  have ha : 0 < a := critical_cycle_decay_pos k
  refine ⟨(C*K^(k+1))*(1+1/a)^k,Z,by positivity,hZ,?_⟩
  intro grid w hw n M B hM hBn hzB v hv
  let S := criticalBlock n M B
  let U := Finset.univ.filter (fun u : Fin k → Fin n =>
    Injective u ∧ (∀ i, u i < v) ∧ ∀ i, (Fin.cons v u : Fin (k+1) → Fin n) i ∈ S)
  let l : Fin n → ℝ := fun i => (i.val : ℝ)+1
  let z := Real.log ((n : ℝ)/l v)
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt v.isLt)
  have hl (i : Fin n) : 0 < l i := by dsimp [l]; positivity
  have hM1 : 1 ≤ M := by omega
  have hz : 1 ≤ z := by
    have hh := hzB.trans (critical_block_log_lower hM1 hv)
    dsimp [z,l]
    linarith
  have hmatrix (i j : Fin n) (hj : j ∈ S) :
      insertionDominationMatrix (w n) (k+1) (k+1) i j ≤ criticalKernel n K gamma (l i) (l j) := by
    have hj' := (Finset.mem_filter.mp hj).2
    exact hmat grid w hw n i j (by omega) (by omega)
      (hzB.trans (critical_block_log_lower hM1 hj))
  have htuples : (∑ u ∈ U, ∏ b : Fin (k+1), insertionDominationMatrix (w n) (k+1) (k+1)
      ((Fin.cons v u : Fin (k+1) → Fin n) b) ((Fin.snoc u v : Fin (k+1) → Fin n) b)) ≤
      ((C*K^(k+1))*z^(-(3/2 : ℝ))/l v)*
        (∑ u ∈ U, ∏ i, (1/l (u i))*(l (u i)/l v)^a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    obtain ⟨hui,huv,huS⟩ := (Finset.mem_filter.mp hu).2
    have htS (b : Fin (k+1)) : (Fin.snoc u v : Fin (k+1) → Fin n) b ∈ S := by
      refine Fin.lastCases ?_ (fun i => ?_) b
      · simpa only [Fin.snoc_last,Fin.cons_zero] using huS 0
      · simpa only [Fin.snoc_castSucc,Fin.cons_succ] using huS i.succ
    have hprod := Finset.prod_le_prod
      (fun b (_ : b ∈ (Finset.univ : Finset (Fin (k+1)))) => insertionDominationMatrix_nonneg (w n) (k+1) (k+1)
        ((Fin.cons v u : Fin (k+1) → Fin n) b) ((Fin.snoc u v : Fin (k+1) → Fin n) b))
      (fun b (_ : b ∈ (Finset.univ : Finset (Fin (k+1)))) => hmatrix
        ((Fin.cons v u : Fin (k+1) → Fin n) b) ((Fin.snoc u v : Fin (k+1) → Fin n) b) (htS b))
    have hcons (b : Fin (k+1)) : l ((Fin.cons v u : Fin (k+1) → Fin n) b) =
        (Fin.cons (l v) (fun i => l (u i)) : Fin (k+1) → ℝ) b := by
      refine Fin.cases rfl (fun _ => rfl) b
    have hsnoc (b : Fin (k+1)) : l ((Fin.snoc u v : Fin (k+1) → Fin n) b) =
        (Fin.snoc (fun i => l (u i)) (l v) : Fin (k+1) → ℝ) b := by
      refine Fin.lastCases ?_ (fun i => ?_) b <;> simp only [Fin.snoc_last,Fin.snoc_castSucc]
    simp only [hcons,hsnoc] at hprod
    apply hprod.trans
    exact hcycle n K (l v) hn hK (hl v) hz (fun i => l (u i)) (fun i => ⟨hl _,by
      dsimp [l]
      have hi : (u i).val ≤ v.val := (huv i).le
      exact_mod_cast Nat.add_le_add_right hi 1⟩)
  have hsum := critical_tuple_weight_sum v ha U (fun u hu i => (Finset.mem_filter.mp hu).2.2.1 i |>.le)
  have hroot := (critical_retained_probability_le_matrix (w n) k S v).trans htuples
  have hb := hroot.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  convert hb using 1 <;> first | rfl | (dsimp [z,l]; ring)

end Luce.Section6
