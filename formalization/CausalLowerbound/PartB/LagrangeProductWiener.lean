import CausalLowerbound.PartB.LagrangeCoefficients
import CausalLowerbound.PartB.TaperedProductWiener
import CausalLowerbound.WienerFiniteCombination

/-! Uniform Wiener control for products of actual Lagrange coefficients.
The finite coefficient expansion is proved, not assumed. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener ConfigurationShells
variable {V E S d : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype S] [DecidableEq S] [Fintype d] [DecidableEq d]

abbrev LagrangeSelections (a b : E → V) (sites : S → V) (d : Type*) :=
  (i : S) → {e : E // incident a b (sites i) e} → Option (d × Bool)

def selectionTags (a b : E → V) (sites : S → V) (s : LagrangeSelections a b sites d)
    (p : IncidentFactorIndex a b sites) : Bool × Option (d × Bool) :=
  (incidentOrientation b (sites p.1) p.2.val, s p.1 p.2)

def productSelectionWeight (a b : E → V) (sites : S → V) (ν : S → d × Bool →₀ ℕ)
    (s : LagrangeSelections a b sites d) : ℝ := ∏ i, selectionWeight (ν i) (s i)

def taperedLagrangeProduct (a b : E → V) (sites : S → V) (ν : S → d × Bool →₀ ℕ)
    (t : ℝ) (u : V × d → ℝ) : ℝ :=
  graphTaper a b taperCutoff t (graphDistance a b u) * ∏ i, lagrangeCoefficient a b (sites i) (ν i) u

theorem tapered_lagrange_expansion (a b : E → V) (sites : S → V) (ν : S → d × Bool →₀ ℕ)
    (t : ℝ) (u : V × d → ℝ) :
    taperedLagrangeProduct a b sites ν t u =
      ∑ s : LagrangeSelections a b sites d, productSelectionWeight a b sites ν s *
        taperedIncidentProduct a b sites (selectionTags a b sites s) t u := by
  unfold taperedLagrangeProduct
  simp_rw [lagrange_coefficient_expansion]
  rw [Fintype.prod_sum (fun (i : S) (s : {e : E // incident a b (sites i) e} → Option (d × Bool)) =>
    selectionWeight (ν i) s * ∏ e, graphFactor a b (e.val, incidentOrientation b (sites i) e.val, s e) u)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_mul_distrib]
  unfold productSelectionWeight taperedIncidentProduct
  simp only [Fintype.prod_sigma, incidentFactor, selectionTags]
  ring

/-- This is the full tapered coefficient-product estimate, after summing
all shells and all elementary terms in every Lagrange coefficient. -/
theorem tapered_lagrange_product_wiener (a b : E → V) (sites : S → V) (ν : S → d × Bool →₀ ℕ) :
    ∃ B ≥ 0, ∀ t > 0, ∃ A : Fourier (V × d),
      (∀ u, toContinuous A (torusProjection u) = (taperedLagrangeProduct a b sites ν t u : ℝ)) ∧
      ‖A‖ ≤ B * ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E *
        ((2 : ℝ) ^ Fintype.card E / t) ^ Fintype.card S := by
  classical
  choose B hB hb using fun s : LagrangeSelections a b sites d =>
    tapered_incident_product_wiener a b sites (selectionTags a b sites s)
  let w := productSelectionWeight a b sites ν
  let C : ℝ := ∑ s, |w s| * B s
  have hC : 0 ≤ C := Finset.sum_nonneg (fun s _ => mul_nonneg (abs_nonneg _) (hB s))
  refine ⟨C, hC, ?_⟩
  intro t ht
  obtain ⟨A, hA, hn⟩ := finite_real_combination_wiener w
    (fun s => taperedIncidentProduct a b sites (selectionTags a b sites s) t)
    (fun s => B s * ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E *
      ((2 : ℝ) ^ Fintype.card E / t) ^ Fintype.card S) (fun s => hb s t ht)
  refine ⟨A, ?_, ?_⟩
  · intro u
    rw [hA, tapered_lagrange_expansion]
  · exact hn.trans_eq (by dsimp [C]; simp only [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; ring)

end CausalLowerbound.PartB.ShellGeometry
