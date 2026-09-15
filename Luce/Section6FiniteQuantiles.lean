import Luce.Section6FinitePopulationOrder

noncomputable section
open Set
namespace Luce.Section6

/-- Deterministic inverse of the actual finite arrival population.
No inverse property is assumed; the following theorems prove it. -/
def arrivalQuantile {n : ℕ} (w : Weights n) (x : ℝ) : ℝ :=
  Function.invFunOn (populationG w) (Ici 0) x

/-- The survivor inverse uses the proved identity H_n=1-G_n. -/
def survivorQuantile {n : ℕ} (w : Weights n) (x : ℝ) : ℝ :=
  arrivalQuantile w (1-x)

def leftQuantileTime {n : ℕ} (w : Weights n) (m : ℕ) : ℝ :=
  arrivalQuantile w ((m : ℝ)/n)

def rightQuantileTime {n : ℕ} (w : Weights n) (m : ℕ) : ℝ :=
  survivorQuantile w ((m : ℝ)/n)

theorem arrivalQuantile_nonneg {n : ℕ} (hn : 0 < n) (w : Weights n) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) : 0 ≤ arrivalQuantile w x :=
  Function.invFunOn_mem (exists_populationG_eq hn w hx)

theorem populationG_arrivalQuantile {n : ℕ} (hn : 0 < n) (w : Weights n) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) : populationG w (arrivalQuantile w x) = x :=
  Function.invFunOn_eq (exists_populationG_eq hn w hx)

theorem arrivalQuantile_populationG {n : ℕ} (hn : 0 < n) (w : Weights n) {t : ℝ}
    (ht : 0 ≤ t) : arrivalQuantile w (populationG w t) = t := by
  have hi : InjOn (populationG w) (Ici 0) :=
    fun _ _ _ _ he => (populationG_strictMono hn w).injective he
  exact hi.leftInvOn_invFunOn ht

theorem arrivalQuantile_pos {n : ℕ} (hn : 0 < n) (w : Weights n) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < arrivalQuantile w x := by
  have hnonneg := arrivalQuantile_nonneg hn w ⟨hx.1.le, hx.2⟩
  have he := populationG_arrivalQuantile hn w ⟨hx.1.le, hx.2⟩
  by_contra hle
  have hz : arrivalQuantile w x = 0 := le_antisymm (le_of_not_gt hle) hnonneg
  rw [hz, populationG_zero] at he
  linarith [hx.1]

theorem survivorQuantile_nonneg {n : ℕ} (hn : 0 < n) (w : Weights n) {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) : 0 ≤ survivorQuantile w x :=
  arrivalQuantile_nonneg hn w ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem populationH_survivorQuantile {n : ℕ} (hn : 0 < n) (w : Weights n) {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) : populationH w (survivorQuantile w x) = x := by
  have hh := populationG_arrivalQuantile hn w
    (x := 1-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [populationG_eq_one_sub_H hn w] at hh
  change populationH w (arrivalQuantile w (1-x)) = x
  linarith

theorem survivorQuantile_pos {n : ℕ} (hn : 0 < n) (w : Weights n) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < survivorQuantile w x :=
  arrivalQuantile_pos hn w ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem survivorQuantile_populationH {n : ℕ} (hn : 0 < n) (w : Weights n) {t : ℝ}
    (ht : 0 ≤ t) : survivorQuantile w (populationH w t) = t := by
  unfold survivorQuantile
  rw [← populationG_eq_one_sub_H hn w]
  exact arrivalQuantile_populationG hn w ht

theorem arrivalQuantile_le_iff {n : ℕ} (hn : 0 < n) (w : Weights n) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (t : ℝ) :
    arrivalQuantile w x ≤ t ↔ x ≤ populationG w t := by
  have hh := (populationG_strictMono hn w).le_iff_le
    (a := arrivalQuantile w x) (b := t)
  rw [populationG_arrivalQuantile hn w hx] at hh
  exact hh.symm

theorem survivorQuantile_le_iff {n : ℕ} (hn : 0 < n) (w : Weights n) {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) (t : ℝ) :
    survivorQuantile w x ≤ t ↔ populationH w t ≤ x := by
  have hh := (populationH_strictAnti hn w).le_iff_ge
    (a := t) (b := survivorQuantile w x)
  rw [populationH_survivorQuantile hn w hx] at hh
  exact hh.symm

theorem leftQuantileTime_spec {n m : ℕ} (w : Weights n) (hm : 0 < m) (hmn : m < n) :
    0 < leftQuantileTime w m ∧ populationG w (leftQuantileTime w m) = (m : ℝ)/n := by
  have hn : 0 < n := hm.trans hmn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hx : (m : ℝ)/n ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (Nat.cast_pos.mpr hm) hnR, (div_lt_one hnR).mpr (by exact_mod_cast hmn)⟩
  exact ⟨arrivalQuantile_pos hn w hx, populationG_arrivalQuantile hn w ⟨hx.1.le, hx.2⟩⟩

theorem rightQuantileTime_spec {n m : ℕ} (w : Weights n) (hm : 0 < m) (hmn : m < n) :
    0 < rightQuantileTime w m ∧ populationH w (rightQuantileTime w m) = (m : ℝ)/n := by
  have hn : 0 < n := hm.trans hmn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hx : (m : ℝ)/n ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (Nat.cast_pos.mpr hm) hnR, (div_lt_one hnR).mpr (by exact_mod_cast hmn)⟩
  exact ⟨survivorQuantile_pos hn w hx, populationH_survivorQuantile hn w ⟨hx.1, hx.2.le⟩⟩

end Luce.Section6
