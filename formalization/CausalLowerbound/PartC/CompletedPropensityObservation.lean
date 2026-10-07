import CausalLowerbound.PartC.PhysicalPropensityRawCell
import CausalLowerbound.PartC.TaperedObservationNormalization
import CausalLowerbound.PartC.PhysicalPatternIntegrands
import CausalLowerbound.PartC.PropensityObservationExpansion

/-! The actual completed propensity likelihood expands into normalized
ghost-pattern integrands. The cutoff mask is removed only together with
the tapered weights, and the normalization cancels per selected site. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem completed_propensity_normalized_expansion
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N ja b t τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ghost : ∀ k, G k → d → ℝ) :
    blockPolynomialFunctional (fun k => physicalPropensityPatternFunctional Q ρ x₀ ℓ r h k.val
      c w N ja t τ (B k) ζ (completedConfiguration (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)))
      (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y) =
      (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)).expect (fun ξ =>
        ∑ s : I → Option S,
          choiceBase (fun i => eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
            (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))) s *
          (t ^ choiceDegree s * ∏ i : ShiftPositions s,
            mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i.val) (y i.val) (choiceSite s i).val 1) *
          ∏ k : S, physicalGhostPatternIntegrand Q x₀ ℓ r h k.val c w N ja τ (B k) (e k)
            (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) ζ ζ
            ((observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x (e k)))
            (ghost k)) := by
  let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let u := fun k : S => completedConfiguration (e k) (u₀ k) (ghost k)
  let slot := fun k : S => retainedObservationSlot Q hQ x₀ r k.val x (e k)
  let χ := fun k : S => completeTaper Q τ (u k)
  let κ := fun k : S => physicalPropensitySlotCorrection x₀ r h k.val c w N ja (u k)
  let z := fun (k : S) v => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (configurationSite (u k) v)
  let pw := fun k : S => propensityPatternWeight (κ k) (B k) (u k) (z k) ζ
  let Δ := fun (i : I) (k : S) => mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i) (y i) k.val 1
  have hd (i : I) (k : S) (a : ℝ) :
      mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i) (y i) k.val a = Δ i k * a := by
    simp only [Δ, mixedPropensityCellIncrement, mul_one]
  have hslot (k : S) (i j : I) (hi : Δ i k ≠ 0) (hj : Δ j k ≠ 0)
      (he : slot k i = slot k j) : i = j :=
    retainedObservationSlot_injective_on_incident Q hQ x₀ r k.val x (e k) i j
      (mixedPropensityCellIncrement_nonzero_incident x₀ ℓ r h ja b ζ (x i) (y i) k.val 1 hi)
      (mixedPropensityCellIncrement_nonzero_incident x₀ ℓ r h ja b ζ (x j) (y j) k.val 1 hj) he
  have he := completed_propensity_pattern_expansion Q hQ side S
    (fun _ => paperCoefficientLaw Q) (fun _ => paperCoefficientAtoms Q ρ)
    x₀ ℓ r h ja b t τ ζ x y G e ghost (fun _ => t * N) pw
  refine he.trans ?_
  apply FiniteLaw.expect_congr
  intro ξ
  apply Finset.sum_congr rfl
  intro s _
  let base := choiceBase (fun i => eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
    (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))) s
  change (base * ∏ i : ShiftPositions s,
    mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i.val) (y i.val) (choiceSite s i).val
      (if χ (choiceSite s i) = 0 then 0 else t * N)) *
        (∏ k, taperedPatternWeight (χ k) (pw k) ((observationChoiceSet s k).image (slot k))) = _
  simp_rw [hd]
  rw [mul_assoc, tapered_observation_unmask χ (fun _ => t * N) Δ pw slot s]
  have hn := tapered_observation_pattern_normalization t N Δ slot hslot χ κ B u z ζ s
  simp only [mul_comm (t * N)] at hn
  rw [hn]
  simp only [physicalGhostPatternIntegrand_diagonal, mul_one]
  dsimp only [base, u₀, u, slot, χ, κ, z, pw, Δ]
  ring

end CausalLowerbound.PartC
