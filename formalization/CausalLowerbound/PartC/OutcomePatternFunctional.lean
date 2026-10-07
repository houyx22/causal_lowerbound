import CausalLowerbound.PartC.TaperedCubicFunctional
import CausalLowerbound.PartC.OutcomeFullMomentFunctional
import CausalLowerbound.PartC.CarrierPermutationSymmetry

/-! The full physical cubic moment is a probability average over slot
permutations of tapered cubic functionals. Its zero pattern reproduces
the actual design carrier, using the symmetry of the atom series. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def physicalOutcomePatternFunctional (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ)
    (k : d → ℤ) (c w N t τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : Fin Q × d → ℝ) :
    MvPolynomial (CoefficientExponent d Q) ℝ →ₗ[ℝ] ℝ :=
  (cubicSiteFunctional (taperedCubicWeight (completeTaper Q τ u)
    (outcomePatternWeight
      (fun i => normalizedRoughVariance x₀ r h k c w N (configurationSite u i)) B u
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (configurationSite u i)) ζ))).comp
    (coefficientShiftAverage (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ)
      (fun a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree (d := d) (Q := Q) a) u)
      (t * N))

set_option maxHeartbeats 800000 in
theorem physicalOutcomeFullFunctional_permutations
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ t τ : ℝ)
    (H : DiscreteLaw ℕ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hseries : HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom unit
      (pairedAtom reflection (naturalPhysicalAtom (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ)) n) B)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : Fin Q × d → ℝ) :
    physicalOutcomeFullFunctional Q ρ x₀ ℓ r h k c w N t τ B ζ u =
      ∑ σ : Equiv.Perm (Fin Q), (permutationLaw (Fin Q)).weight σ •
        physicalOutcomePatternFunctional Q ρ x₀ ℓ r h k c w N t τ B ζ
          (fun p => u (σ p.1, p.2)) := by
  apply LinearMap.ext
  intro p
  rw [physicalOutcomeFullFunctional_apply]
  let z := fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u (j, a))
  have hsym (σ : Equiv.Perm (Fin Q)) :
      pointValue (torusProjection (fun v => u (σ v.1, v.2))) (fun j => z (σ j)) ζ B =
        physicalCarrierValue x₀ ℓ r h k c w N B ζ u :=
    carrier_series_value_symmetric x₀ ℓ r h k c w N θ H B hseries (torusProjection u) z ζ σ
  have hterm (σ : Equiv.Perm (Fin Q)) :=
    taperedCubicFunctional_shift_average (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ)
      (fun a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree a)
        (fun v => u (σ v.1, v.2))) (t * N)
      (graphTaper edgeLeft edgeRight taperCutoff τ
        (graphDistance edgeLeft edgeRight (fun v => u (σ v.1, v.2))))
      (outcomePatternWeight
        (fun i => normalizedRoughVariance x₀ r h k c w N (fun j => u (σ i, j))) B
        (fun v => u (σ v.1, v.2)) (fun j => z (σ j)) ζ) p
  simp only [show (0 : Degree (Fin Q) 3) = (fun _ => 0) from rfl,
    outcomePatternWeight_zero, hsym] at hterm
  dsimp only [z] at hterm
  have hterm' (σ : Equiv.Perm (Fin Q)) :
      physicalOutcomePatternFunctional Q ρ x₀ ℓ r h k c w N t τ B ζ
        (fun v => u (σ v.1, v.2)) p =
      physicalCarrierValue x₀ ℓ r h k c w N B ζ u *
        (paperCoefficientLaw Q).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p) +
      outcomeCoefficientFunctional edgeLeft edgeRight (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ)
        polynomialBasisDegree (t * N) τ
        (fun i => normalizedRoughVariance x₀ r h k c w N (fun j => u (σ i, j))) B
        (fun v => u (σ v.1, v.2))
        (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u (σ i, j))) ζ p := by
    simpa only [physicalOutcomePatternFunctional, LinearMap.comp_apply,
      outcomeCoefficientFunctional, LinearMap.smul_apply, smul_eq_mul,
      completeTaper, configurationSite, outcomePolynomialFunctional] using hterm σ
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, permutationLaw,
    hterm', ← Finset.mul_sum, paperPhysicalOutcomePolynomial, configurationSite,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card (Equiv.Perm (Fin Q)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hn]
  <;> ring_nf <;> rfl

end CausalLowerbound.PartC
