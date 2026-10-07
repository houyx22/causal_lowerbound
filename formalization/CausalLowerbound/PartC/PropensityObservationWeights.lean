import CausalLowerbound.PartC.ObservationBlockChoices
import CausalLowerbound.PartC.GlobalPropensityShift

/-! The actual coefficients in the observation-pattern expansion. For the
baseline side, every observation supplies its rough propensity factor;
the remaining coefficient is independent of the shared rough signs. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial
variable {d I K : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

theorem choice_rough_factorization (f a : I → ℝ) (δ : I → K → ℝ) (s : I → Option K) :
    choiceBase (fun i => f i * a i) s * (∏ i : ShiftPositions s, f i.val * δ i.val (choiceSite s i)) =
      (choiceBase a s * ∏ i : ShiftPositions s, δ i.val (choiceSite s i)) * ∏ i, f i := by
  simp only [choiceBase, Finset.prod_mul_distrib]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => (s i).isSome) f]
  ring

def propensityObservationCoefficient (Q : ℕ) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) (s : I → Option S) : ℝ :=
  choiceBase (fun i => eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
    (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))) s *
      (t ^ choiceDegree s * ∏ i : ShiftPositions s,
        mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i.val) (y i.val) (choiceSite s i).val 1)

def propensityChoiceSmoothCoefficient (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r b : ℝ) (x : I → d → ℝ) (y : I → Bool × Bool)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) (s : I → Option S) : ℝ :=
  choiceBase (fun i => (1 / 4) * (1 + sign (y i).2 * b *
    eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))) s *
      ∏ i : ShiftPositions s, (1 / 4) * sign (y i.val).2 * b *
        linearPartition (localCoordinate x₀ r (choiceSite s i).val (x i.val))

theorem propensityObservationCoefficient_false (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) (s : I → Option S) :
    propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s =
      propensityChoiceSmoothCoefficient Q ρ S x₀ r b x y ξ s * t ^ choiceDegree s *
        ∏ i, (1 + sign (y i).1 * ja * physicalRoughField x₀ ℓ h ζ (x i)) := by
  let f := fun i => 1 + sign (y i).1 * ja * physicalRoughField x₀ ℓ h ζ (x i)
  let a := fun i => (1 / 4) * (1 + sign (y i).2 * b *
    eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
  let Δ := fun (i : I) (k : S) => (1 / 4) * sign (y i).2 * b * linearPartition (localCoordinate x₀ r k.val (x i))
  have hp (i : I) : eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (mixedPropensityCellPolynomial Q false S x₀ ℓ r h ja b t ζ (x i) (y i)) = f i * a i := by
    simp only [mixedPropensityCellPolynomial, map_mul, eval_C, propensitySitePolynomial_eval,
      Bool.false_eq_true, if_false, add_zero, RoughPropensity.likelihood, f, a]
    ring
  have hd (i : I) (k : S) :
      mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i) (y i) k.val 1 = f i * Δ i k := by
    simp only [mixedPropensityCellIncrement, f, Δ]
    ring
  unfold propensityObservationCoefficient
  simp_rw [hp, hd]
  calc
    _ = t ^ choiceDegree s * (choiceBase (fun i => f i * a i) s *
        ∏ i : ShiftPositions s, f i.val * Δ i.val (choiceSite s i)) := by ring
    _ = _ := by
      rw [choice_rough_factorization]
      change t ^ choiceDegree s * (propensityChoiceSmoothCoefficient Q ρ S x₀ r b x y ξ s * ∏ i, f i) = _
      ring

end CausalLowerbound.PartC
