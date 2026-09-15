import Luce.Section6MonotoneQuadrature
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Luce.Section6

theorem positive_natset_order_bound (s : Finset ℕ) (hs : ∀ k ∈ s, 0 < k)
    (i : Fin s.card) : i.val+1 ≤ s.orderEmbOfFin rfl i := by
  have hseq : ∀ k : ℕ, ∀ hk : k < s.card, k+1 ≤ s.orderEmbOfFin rfl ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact hs _ (s.orderEmbOfFin_mem rfl ⟨0, hk⟩)
    | succ k ih =>
      intro hk
      have hk' : k < s.card := Nat.lt_trans (Nat.lt_succ_self k) hk
      have hlo := ih hk'
      have hstep := (s.orderEmbOfFin rfl).strictMono
        (show (⟨k, hk'⟩ : Fin s.card) < ⟨k+1, hk⟩ from Nat.lt_succ_self k)
      omega
  exact hseq i.val i.isLt

/-- Any h distinct positive depths have at least the power sum of the
first h depths, which dominates the integral of x^beta. -/
theorem positive_natset_rpow_sum_ge (s : Finset ℕ) (hs : ∀ k ∈ s, 0 < k)
    {beta : ℝ} (hb : 0 < beta) :
    (s.card : ℝ)^(beta+1)/(beta+1) ≤ ∑ k ∈ s, (k : ℝ)^beta := by
  have hsum : (∑ i : Fin s.card, ((i.val : ℝ)+1)^beta) ≤ ∑ k ∈ s, (k : ℝ)^beta := by
    calc
      _ ≤ ∑ i : Fin s.card, (s.orderEmbOfFin rfl i : ℝ)^beta := by
        apply Finset.sum_le_sum
        intro i _
        apply Real.rpow_le_rpow (by positivity) _ hb.le
        exact_mod_cast positive_natset_order_bound s hs i
      _ = _ := by
        have heq : (∑ k ∈ Finset.univ.map (s.orderEmbOfFin rfl).toEmbedding, (k : ℝ)^beta) =
            ∑ i : Fin s.card, (s.orderEmbOfFin rfl i : ℝ)^beta := by rw [Finset.sum_map]; rfl
        rw [s.map_orderEmbOfFin_univ rfl] at heq
        exact heq.symm
  have hm : MonotoneOn (fun x : ℝ => x^beta) (Icc (0 : ℝ) (0+s.card)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow hx.1 hxy hb.le
  have hi := hm.integral_le_sum
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at hi
  rw [integral_rpow (Or.inl (by linarith)),
    Real.zero_rpow (by linarith : beta+1 ≠ 0), sub_zero] at hi
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((i : ℝ)+1)^beta) s.card] at hsum
  exact hi.trans hsum

end Luce.Section6
