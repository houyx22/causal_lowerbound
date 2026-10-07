import CausalLowerbound.PartC.OutcomeObservationExpansion
import CausalLowerbound.PartC.OutcomePatternFunctional
import CausalLowerbound.PartC.CubicObservationMasks
import CausalLowerbound.PartC.CubicObservationRescaling
import CausalLowerbound.PartC.PhysicalOutcomePatternIntegrands

/-! The completed rough-outcome observation polynomial uses the actual
normalized cubic integrands and the effective physical shift a*t.
The amplitude mask disappears together with the tapered weights. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem completed_outcome_normalized_expansion
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N a jb t τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ghost : ∀ k, G k → d → ℝ) :
    blockPolynomialFunctional (fun k => physicalOutcomePatternFunctional Q ρ x₀ ℓ r h k.val
      c w N t τ (B k) ζ (completedConfiguration (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)))
      (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y) =
      (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)).expect (fun ξ =>
        (1 / 4 : ℝ) ^ Fintype.card I * blockPolynomialFunctional
          (fun k => normalizedPhysicalOutcomeCubicFunctional Q x₀ ℓ r h k.val c w N τ (B k) (e k)
            (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
            (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
              (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) ζ (ghost k))
          (∏ i, outcomeTaylorPolynomial (sign (y i).1) (sign (y i).2) 1 jb
            (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
            (a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
              (globalCarriedPolynomial Q S x₀ r (x i)))
            (physicalRoughField x₀ ℓ h ζ (x i))
            (∑ k : S, C ((a * t) * linearPartition (localCoordinate x₀ r k.val (x i))) *
              X (k, retainedObservationSlot Q hQ x₀ r k.val x (e k) i)))) := by
  let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let u := fun k : S => completedConfiguration (e k) (u₀ k) (ghost k)
  let slot := fun k : S => retainedObservationSlot Q hQ x₀ r k.val x (e k)
  let χ := fun k : S => completeTaper Q τ (u k)
  let κ := fun (k : S) v => normalizedRoughVariance x₀ r h k.val c w N (configurationSite (u k) v)
  let z := fun (k : S) v => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (configurationSite (u k) v)
  let pw := fun k : S => outcomePatternWeight (κ k) (B k) (u k) (z k) ζ
  let δ := fun (i : I) (k : S) => linearPartition (localCoordinate x₀ r k.val (x i))
  have he := completed_outcome_tapered_expansion Q hQ S
    (fun _ => paperCoefficientLaw Q) (fun _ => paperCoefficientAtoms Q ρ)
    x₀ ℓ r h a jb t τ ζ x y G e ghost (fun _ => t * N) pw
  refine he.trans ?_
  apply FiniteLaw.expect_congr
  intro ξ
  apply congrArg (fun v : ℝ => (1 / 4 : ℝ) ^ Fintype.card I * v)
  have hmask (i : I) (k : S) :
      a * δ i k * (if χ k = 0 then 0 else t * N) =
        (if χ k = 0 then 0 else ((a * t) * N) * δ i k) := by
    split_ifs <;> ring
  change blockPolynomialFunctional (fun k => cubicSiteFunctional (taperedCubicWeight (χ k) (pw k)))
    (∏ i, outcomeTaylorPolynomial (sign (y i).1) (sign (y i).2) 1 jb
      (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
      (a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i)))
      (physicalRoughField x₀ ℓ h ζ (x i))
      (∑ k : S, C (a * δ i k * (if χ k = 0 then 0 else t * N)) * X (k, slot k i))) = _
  simp_rw [hmask]
  rw [block_outcome_taylor_unmask]
  have hr := block_outcome_taylor_rescale (fun k => taperedCubicWeight (χ k) (pw k))
    (fun i => sign (y i).1) (fun i => sign (y i).2) (fun _ => jb)
    (fun i => physicalRoughCorrection x₀ ℓ h (a * t) (x i))
    (fun i => a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (globalCarriedPolynomial Q S x₀ r (x i)))
    (fun i => physicalRoughField x₀ ℓ h ζ (x i)) δ slot (a * t) N
  refine hr.trans ?_
  have hL : (fun k : S => cubicSiteFunctional (fun f => N ^ degreeSize f *
      taperedCubicWeight (χ k) (pw k) f)) =
      (fun k => normalizedPhysicalOutcomeCubicFunctional Q x₀ ℓ r h k.val c w N τ (B k) (e k) (u₀ k)
        (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i)) ζ (ghost k)) := by
    funext k
    exact (normalizedPhysicalOutcomeCubicFunctional_diagonal Q x₀ ℓ r h k.val c w N τ
      (B k) (e k) (u₀ k) ζ (ghost k)).symm
  rw [hL]

end CausalLowerbound.PartC
