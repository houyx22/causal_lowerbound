import CausalLowerbound.PartC.BlockPolynomialMap
import CausalLowerbound.PartC.RetainedCubicFunctional
import CausalLowerbound.PartC.BlockCubicFunctional

/-! Pull every completed carrier back to common observation indices.
This retains all cubic mixed block monomials, and expands each actual
completed carrier into its finite Fourier-Walsh rows. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Wiener Representative
variable {K I V d J : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
  [Fintype d] [Fintype J] [DecidableEq J]

theorem blockPolynomialFunctional_retained_cubic_map
    (P : K → I → Prop) (G : K → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k, {i // P k i} ⊕ G k ≃ V) (w : K → Degree V 3 → ℝ)
    (p : MvPolynomial (K × I) ℝ) :
    blockPolynomialFunctional (fun k => cubicSiteFunctional (w k))
      (blockPolynomialMap (fun k => retainedPolynomialMap (P k) (e k)) p) =
      cubicSiteFunctional (fun f => ∏ k, retainedCubicWeight (P k) (e k) (w k) (fun i => f (k, i))) p := by
  rw [blockPolynomialFunctional_map]
  have he : (fun k => (cubicSiteFunctional (w k)).comp (retainedPolynomialMap (P k) (e k)).toLinearMap) =
      (fun k => cubicSiteFunctional (retainedCubicWeight (P k) (e k) (w k))) := by
    funext k
    apply LinearMap.ext
    intro q
    exact cubicSiteFunctional_retained_map (P k) (e k) (w k) q
  rw [he, blockPolynomialFunctional_cubic_patterns]

theorem blockOutcomeFunctional_retained_map
    (P : K → I → Prop) (G : K → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k, {i // P k i} ⊕ G k ≃ V) (κ : K → V → ℝ) (v a : K → I → ℝ)
    (hκ : ∀ k (i : {i // P k i}), κ k (e k (Sum.inl i)) = v k i.val)
    (ha : ∀ k i, ¬P k i → a k i = 0)
    (W : K → Array d V J 3) (u : K → V × d → ℝ) (ζ : J → Bool)
    (g : ∀ k, G k → ℝ) (p : MvPolynomial (K × I) ℝ) :
    blockPolynomialFunctional (fun k => outcomePolynomialFunctional (κ k) (W k) (u k)
      (completedSites (e k) (fun i => a k i.val) (g k)) ζ)
      (blockPolynomialMap (fun k => retainedPolynomialMap (P k) (e k)) p) =
      cubicSiteFunctional (fun f => ∏ k, ∑ r : Row V J 3,
        completedOutcomeRowCoefficient (W k) (u k) ζ (e k) (g k) r *
          ∏ i, if f (k, i) = 0 then a k i ^ (retainedOutcomeRowDegree (P k) (e k) r.1 i).val else
            outcomeMoment (v k i) (retainedOutcomeRowDegree (P k) (e k) r.1 i) * a k i ^ (f (k, i)).val) p := by
  simp only [outcomePolynomialFunctional]
  rw [blockPolynomialFunctional_retained_cubic_map P G e]
  apply congrArg (fun w : Degree (K × I) 3 → ℝ => cubicSiteFunctional w p)
  funext f
  apply Finset.prod_congr rfl
  intro k _
  exact retainedCubicWeight_outcome_rows (P k) (e k) (κ k) (v k) (a k)
    (hκ k) (ha k) (W k) (u k) ζ (g k) (fun i => f (k, i))

end CausalLowerbound.PartC
