import CausalLowerbound.PartC.PropensityMomentWitness
import CausalLowerbound.PartC.BlockFunctionalMeasure
import CausalLowerbound.PartC.DesignWeightedPolynomialMoments

/-! Exact passage from the actual design-weighted prior to one joint ghost
integral. Integrability is derived from the constructed carrier moment
witness; the shared sign average remains outside all block operations. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I]

theorem raw_propensity_full_integral
    (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c w N N₀ θ ja t τ K δ : ℝ)
    (hθ : 0 ≤ θ)
    (hcarr : ∀ k : S, HasPaperPropensityCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ ja t τ K δ)
    (R : ∀ k : S, PropensityMomentWitness Q ρ x₀ ℓ r h k.val c w N θ ja t τ)
    (F : ((S → ℕ) × (activeBlocks (d := d) ℓ h → Bool)) → CarrierProfile d θ)
    (hF : ∀ labels ζ (k : S) u, (F (labels, ζ)).density k.val u =
      carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k.val c w N θ (labels k) ζ u)
    (x : I → d → ℝ) (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (p : (activeBlocks (d := d) ℓ h → Bool) → MvPolynomial (S × CoefficientExponent d Q) ℝ)
    (hp : ∀ ζ, (p ζ).totalDegree ≤ 4 * Q) :
    (signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (fun v =>
      (∏ i, (F v.1).product S x₀ r (x i)) *
        eval (fun ka => paperCoefficientAtoms Q ρ (v.2 ka.1) ka.2) (p v.1.2)) =
      independentSigns.expect (fun ζ =>
        ∫ ghost : ∀ k, G k → d → ℝ,
          blockPolynomialFunctional (fun k => physicalPropensityFullFunctional Q ρ x₀ ℓ r h k.val
            c w N ja t τ (R k).representative ζ (completedConfiguration (e k)
              (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k))) (p ζ)
          ∂Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) := by
  rw [raw_design_weighted_polynomial_moments S θ hθ F
    (fun k ζ n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k.val c w N θ n ζ)
    hF (fun k => (R k).law) (fun k => (R k).kernel) (paperCoefficientAtoms Q ρ) x₀ r x p]
  apply FiniteLaw.expect_congr
  intro ζ
  let u := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  have hu (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) : u k i ∈ Set.Icc (0 : d → ℝ) 1 :=
    retained_design_chart_mem_cube x₀ r k.val x i
  rw [blockPolynomialFunctional_integral_measure _ _ (p ζ) (fun m hm k =>
    (R k).full_integrable (hcarr k) hθ ζ (e k) (u k) (hu k)
      (blockMonomial m k) ((blockMonomial_degree_le (p ζ) m hm k).trans (hp ζ)))]
  apply Finset.sum_congr rfl
  intro m hm
  apply congrArg (fun a : ℝ => (p ζ).coeff m * a)
  apply Finset.prod_congr rfl
  intro k _
  exact (R k).weighted_projective (hcarr k) hθ ζ (e k) (u k) (hu k)
    (blockMonomial m k) ((blockMonomial_degree_le (p ζ) m hm k).trans (hp ζ))

theorem physical_propensity_block_permutations
    {B : Type*} [Fintype B] [DecidableEq B]
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (block : B → d → ℤ)
    (c w N θ ja t τ : ℝ)
    (R : ∀ k, PropensityMomentWitness Q ρ x₀ ℓ r h (block k) c w N θ ja t τ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : B → Fin Q × d → ℝ)
    (p : MvPolynomial (B × CoefficientExponent d Q) ℝ) :
    blockPolynomialFunctional (fun k => physicalPropensityFullFunctional Q ρ x₀ ℓ r h (block k)
      c w N ja t τ (R k).representative ζ (u k)) p =
      (FiniteLaw.independent (fun _ : B => permutationLaw (Fin Q))).expect (fun σ =>
        blockPolynomialFunctional (fun k => physicalPropensityPatternFunctional Q ρ x₀ ℓ r h (block k)
          c w N ja t τ (R k).representative ζ (fun v => u k (σ k v.1, v.2))) p) := by
  have he (k : B) := physicalPropensityFullFunctional_permutations Q ρ x₀ ℓ r h (block k)
    c w N θ ja t τ (R k).law (R k).representative (R k).atom_series ζ (u k)
  simp_rw [he]
  exact blockPolynomialFunctional_finite_average (fun _ : B => permutationLaw (Fin Q)) _ p

theorem completedConfiguration_permute {A G : Type*} (Q : ℕ)
    (e : A ⊕ G ≃ Fin Q) (u : A → d → ℝ) (g : G → d → ℝ) (σ : Equiv.Perm (Fin Q)) :
    completedConfiguration (e.trans σ.symm) u g =
      fun v => completedConfiguration e u g (σ v.1, v.2) := by
  rfl

end CausalLowerbound.PartC
