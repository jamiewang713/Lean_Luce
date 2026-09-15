import Luce.Section5LateSourceBounds
import Luce.Section5FiniteCover

noncomputable section
open scoped BigOperators
namespace Luce
attribute [local instance] Classical.propDecidable

/-- Combined late contribution for retained predecessors. The finite cover
premise is geometric and the floor thresholds are discharged by the raw
shell condition in the asymptotic application. -/
theorem late_retained_pairs_bound (w : WeightArray) (n J₀ J ell k : ℕ)
    (old : Fin n → ℝ) (hinj : Function.Injective old) (hnonneg : ∀ i, 0 ≤ old i)
    (S S₀ : Finset (Fin n)) {δ : ℝ} (hδ : 0 < δ) (hJ₀ : 1 ≤ J₀) (hJ : 1 ≤ J)
    (hcut : 1 ≤ δ*((J : ℝ) - Real.sqrt J))
    (hrate : ∀ u ∈ S₀, δ ≤ (w n).rate u)
    (hcover : ∀ u ∈ S, u ∈ S₀ ∨ J₀ ≤ terminalShellNumber u)
    (hfloor : ∀ r ∈ Finset.Icc J₀ n, ∀ hs : (terminalShell n r).Nonempty,
      1 < shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) :
    (∑ v ∈ deepShellLabels n J, ∑ u ∈ S.filter (fun u => u < v),
      lateGhostEntry (w n) ell old hinj u v (terminalShellTime v) *
        markedReturnWeight (ghostEntry (w n) ell old) k v u) ≤
      (2*ell+1 : ℕ)^(k+2) *
        (Real.exp (-δ*((J : ℝ) - Real.sqrt J)) +
          ∑ r ∈ Finset.Icc J₀ n, if hs : (terminalShell n r).Nonempty then
            Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0) := by
  let F := fun (v u : Fin n) => if u < v then
    lateGhostEntry (w n) ell old hinj u v (terminalShellTime v) *
      markedReturnWeight (ghostEntry (w n) ell old) k v u else 0
  have hF (v u : Fin n) : 0 ≤ F v u := by
    dsimp [F]
    split_ifs
    · exact mul_nonneg ENNReal.toReal_nonneg
        (markedReturnWeight_nonneg _ (fun u v => (ghostEntry_mem_Icc (w n) ell old u v).1) k v u)
    · exact le_refl 0
  have hcover' (u : Fin n) (hu : u ∈ S) :
      u ∈ S₀ ∨ ∃ r ∈ Finset.Icc J₀ n, u ∈ terminalShell n r := by
    rcases hcover u hu with hu₀ | huJ
    · exact Or.inl hu₀
    · have hmem := mem_terminalShellNumber u (hJ₀.trans huJ)
      exact Or.inr ⟨terminalShellNumber u,
        Finset.mem_Icc.mpr ⟨huJ, shell_index_le_row ⟨u, hmem⟩⟩, hmem⟩
  have hsplit : (∑ v ∈ deepShellLabels n J, ∑ u ∈ S, F v u) ≤
      (∑ v ∈ deepShellLabels n J, ∑ u ∈ S₀, F v u) +
        ∑ r ∈ Finset.Icc J₀ n, ∑ v ∈ deepShellLabels n J,
          ∑ u ∈ terminalShell n r, F v u := by
    have h := Finset.sum_le_sum (fun v (_ : v ∈ deepShellLabels n J) =>
      finite_cover_sum_le S S₀ (Finset.Icc J₀ n) (terminalShell n) (F v) (hF v) hcover')
    rw [Finset.sum_add_distrib,
      Finset.sum_comm (s := deepShellLabels n J) (t := Finset.Icc J₀ n)] at h
    exact h
  have hint : (∑ v ∈ deepShellLabels n J, ∑ u ∈ S₀, F v u) ≤
      (2*ell+1 : ℕ)^(k+2) * Real.exp (-δ*((J : ℝ) - Real.sqrt J)) := by
    simpa only [Finset.sum_filter, F] using
      late_interior_source_bound (w n) J ell k old hinj hnonneg S₀ hδ hJ hcut hrate
  have hterm (r : ℕ) (hr : r ∈ Finset.Icc J₀ n) :
      (∑ v ∈ deepShellLabels n J, ∑ u ∈ terminalShell n r, F v u) ≤
        (2*ell+1 : ℕ)^(k+2) * (if hs : (terminalShell n r).Nonempty then
          Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0) := by
    by_cases hs : (terminalShell n r).Nonempty
    · simpa only [Finset.sum_filter, F, dif_pos hs] using
        late_terminal_source_bound w n r J ell k old hinj hnonneg hJ hs (hfloor r hr hs)
    · rw [dif_neg hs]
      simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty,
        Finset.sum_const_zero, mul_zero, le_refl]
  simp only [Finset.sum_filter]
  change (∑ v ∈ deepShellLabels n J, ∑ u ∈ S, F v u) ≤ _
  apply hsplit.trans
  calc
    _ ≤ (2*ell+1 : ℕ)^(k+2) * Real.exp (-δ*((J : ℝ) - Real.sqrt J)) +
        ∑ r ∈ Finset.Icc J₀ n, (2*ell+1 : ℕ)^(k+2) *
          (if hs : (terminalShell n r).Nonempty then
            Real.exp (-shellFloor w n r hs * ((r : ℝ) - Real.sqrt r)) else 0) :=
      add_le_add hint (Finset.sum_le_sum hterm)
    _ = _ := by rw [← Finset.mul_sum, ← mul_add]

end Luce
