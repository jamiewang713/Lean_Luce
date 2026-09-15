import Luce.Section6OpenSimplex

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators
namespace Luce.Section6

/-- Open-simplex mass extended by zero on tied backgrounds, a proved null
set for the exponential race. -/
def openGapSimplexValue {n r : ℕ} (w : Weights n) (u : Fin r → Fin n)
    (q : Fin r → ℕ) (k : ℕ) (old : Fin n → ℝ) : ℝ :=
  if hold : Injective old then openGapSimplexIntegral w u q k old hold else 0

theorem gapSimplexIntegral_ae_eq_openValue {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) :
    ∀ᵐ old ∂exponentialRace w, ∀ k,
      gapSimplexIntegral w u q k old = openGapSimplexValue w u q k old := by
  filter_upwards [exponentialRace_injective_ae w, exponentialRace_nonnegative_background w]
    with old hold hpos
  intro k
  simp only [openGapSimplexValue, dif_pos hold]
  exact gapSimplexIntegral_eq_open w u q k old hold hpos

/-- The exact ordered-simplex cylinder identity in the manuscript's open
order-statistic gaps, including adjacent ranks and the terminal gap. -/
theorem markedRankCylinder_real_probability_eq_openSimplex_product {n r : ℕ}
    (w : Weights n) (u j : Fin r → Fin n) (hu : Injective u) (hj : Injective j) :
    (exponentialRace w).real {clocks | MarkedRankCylinder u j clocks} =
      ∫ old, ∏ k ∈ Finset.univ.image (sortedMarkedGapIndex j),
        openGapSimplexValue w (u ∘ Tuple.sort j) (sortedMarkedGapIndex j) k old
        ∂exponentialRace w := by
  rw [markedRankCylinder_real_probability_eq_simplex_product w u j hu hj]
  apply integral_congr_ae
  filter_upwards [gapSimplexIntegral_ae_eq_openValue w (u ∘ Tuple.sort j) (sortedMarkedGapIndex j)]
    with old hold
  exact Finset.prod_congr rfl fun k _ => hold k

theorem openGapSimplexProduct_integrable {n r : ℕ} (w : Weights n)
    (u : Fin r → Fin n) (q : Fin r → ℕ) (hu : Injective u) :
    Integrable (fun old => ∏ k ∈ Finset.univ.image q, openGapSimplexValue w u q k old)
      (exponentialRace w) := by
  apply (gapSimplexProduct_integrable w u q hu).congr
  filter_upwards [gapSimplexIntegral_ae_eq_openValue w u q] with old hold
  exact Finset.prod_congr rfl fun k _ => hold k

end Luce.Section6
