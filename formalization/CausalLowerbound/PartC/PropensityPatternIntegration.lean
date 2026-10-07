import CausalLowerbound.PartC.CompletedPropensityObservation

/-! Exchange the finite observation expansion with the true product cube
integral. Every term's integrability follows from the physical integrand
bound, and its integral is a product of the existing ghost pattern weights. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound
namespace FiniteLaw
variable {Ω X : Type*} [Fintype Ω] [MeasurableSpace X]

theorem expect_integrable (μ : FiniteLaw Ω) (ν : Measure X) (f : Ω → X → ℝ)
    (hf : ∀ ω, Integrable (f ω) ν) : Integrable (fun x => μ.expect (fun ω => f ω x)) ν := by
  exact integrable_finset_sum Finset.univ (fun ω _ => (hf ω).const_mul (μ.weight ω))

theorem integral_expect (μ : FiniteLaw Ω) (ν : Measure X) (f : Ω → X → ℝ)
    (hf : ∀ ω, Integrable (f ω) ν) :
    (∫ x, μ.expect (fun ω => f ω x) ∂ν) = μ.expect (fun ω => ∫ x, f ω x ∂ν) := by
  unfold expect
  rw [integral_finset_sum Finset.univ (fun ω _ => (hf ω).const_mul (μ.weight ω))]
  simp only [integral_const_mul]

end FiniteLaw
namespace PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt

theorem finite_pattern_product_integral
    {K A Ω : Type*} [Fintype K] [Fintype A] [Fintype Ω]
    {Z : K → Type*} [∀ k, MeasurableSpace (Z k)]
    (μ : ∀ k, Measure (Z k)) [∀ k, SigmaFinite (μ k)]
    (ν : FiniteLaw Ω) (coeff : Ω → A → ℝ) (f : A → ∀ k, Z k → ℝ)
    (hf : ∀ a k, Integrable (f a k) (μ k)) :
    Integrable (fun z : ∀ k, Z k => ν.expect (fun ω => ∑ a, coeff ω a * ∏ k, f a k (z k))) (Measure.pi μ) ∧
    (∫ z : ∀ k, Z k, ν.expect (fun ω => ∑ a, coeff ω a * ∏ k, f a k (z k)) ∂Measure.pi μ) =
      ν.expect (fun ω => ∑ a, coeff ω a * ∏ k, ∫ z, f a k z ∂μ k) := by
  letI : ∀ k, MeasureSpace (Z k) := fun k => ⟨μ k⟩
  letI : ∀ k, SigmaFinite (volume : Measure (Z k)) := fun k => inferInstanceAs (SigmaFinite (μ k))
  have hp (a : A) : Integrable (fun z : ∀ k, Z k => ∏ k, f a k (z k)) (Measure.pi μ) :=
    Integrable.fintype_prod_dep (hf a)
  have hs (ω : Ω) : Integrable (fun z : ∀ k, Z k => ∑ a, coeff ω a * ∏ k, f a k (z k)) (Measure.pi μ) :=
    integrable_finset_sum Finset.univ (fun a _ => (hp a).const_mul (coeff ω a))
  refine ⟨ν.expect_integrable (Measure.pi μ) _ hs, ?_⟩
  rw [ν.integral_expect (Measure.pi μ) _ hs]
  apply ν.expect_congr
  intro ω
  rw [integral_finset_sum Finset.univ (fun a _ => (hp a).const_mul (coeff ω a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_const_mul]
  apply congrArg (fun b : ℝ => coeff ω a * b)
  exact @integral_fintype_prod_eq_prod ℝ inferInstance K inferInstance Z (f a)
    (fun k => ⟨μ k⟩) (fun k => inferInstanceAs (SigmaFinite (μ k)))

variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem completed_propensity_pattern_integral
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N N₀ ja b t τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hja : ja ^ 2 ≤ 1)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    let P := fun ghost : ∀ k, G k → d → ℝ =>
      blockPolynomialFunctional (fun k => physicalPropensityPatternFunctional Q ρ x₀ ℓ r h k.val
        c w N ja t τ (B k) ζ (completedConfiguration (e k)
          (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)))
        (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y)
    Integrable P (Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) ∧
    (∫ ghost, P ghost ∂Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) =
      (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)).expect (fun ξ =>
        ∑ s : I → Option S,
          choiceBase (fun i => eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
            (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))) s *
          (t ^ choiceDegree s * ∏ i : ShiftPositions s,
            mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i.val) (y i.val) (choiceSite s i).val 1) *
          ∏ k : S, physicalGhostPatternWeight Q x₀ ℓ r h k.val c w N ja τ (B k) (e k)
            (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) ζ ζ
            ((observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x (e k)))) := by
  dsimp only
  let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let coeff := fun (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) (s : I → Option S) =>
    choiceBase (fun i => eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))) s *
        (t ^ choiceDegree s * ∏ i : ShiftPositions s,
          mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i.val) (y i.val) (choiceSite s i).val 1)
  let f := fun (s : I → Option S) (k : S) => physicalGhostPatternIntegrand Q x₀ ℓ r h k.val c w N ja τ
    (B k) (e k) (u₀ k) ζ ζ ((observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x (e k)))
  have hf (s : I → Option S) (k : S) : Integrable (f s k) (Measure.pi (fun _ : G k => cubeMeasure d)) :=
    physicalGhostPatternIntegrand_integrable Q x₀ ℓ r h k.val c w N N₀ ja τ hc hN₀ hN hm hrough hja
      (B k) (e k) (u₀ k) ζ ζ _
  have he : (fun ghost : ∀ k, G k → d → ℝ =>
      blockPolynomialFunctional (fun k => physicalPropensityPatternFunctional Q ρ x₀ ℓ r h k.val
        c w N ja t τ (B k) ζ (completedConfiguration (e k) (u₀ k) (ghost k)))
        (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y)) =
      (fun ghost => (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)).expect
        (fun ξ => ∑ s, coeff ξ s * ∏ k, f s k (ghost k))) := by
    funext ghost
    exact completed_propensity_normalized_expansion Q hQ ρ side S x₀ ℓ r h c w N ja b t τ B ζ x y G e ghost
  rw [he]
  have hi := finite_pattern_product_integral (fun k => Measure.pi (fun _ : G k => cubeMeasure d))
    (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)) coeff f hf
  exact hi

end PartC
end CausalLowerbound
