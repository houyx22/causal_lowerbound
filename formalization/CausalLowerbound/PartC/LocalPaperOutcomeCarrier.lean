import CausalLowerbound.PartC.PaperOutcomeCarrier
import CausalLowerbound.PartC.PhysicalCarrierLocality
import CausalLowerbound.PartC.OutcomeTargetLocality

/-! Localize the chosen coefficient laws without changing the design
mixture, positivity, or any prescribed moment. The original existential
choice of a law need not itself respect locality. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

set_option maxHeartbeats 1200000 in
theorem HasPaperOutcomeCarrier.local_realization
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0) (k : d → ℤ)
    (c w N N₀ θ t τ K δ : ℝ) (hc : 0 < c)
    (hcarr : HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k c w N N₀ θ t τ K δ) :
    let I := MomentExponent (CoefficientExponent d Q) (4 * Q)
    let L := ((Fintype.card I : ℝ) * polarizationBound (Fin Q) θ) * δ
    ∃ (B : Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (H : DiscreteLaw ℕ)
        (kernel : (activeBlocks (d := d) ℓ h → Bool) → ℕ →
          FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      reflection B = B ∧ ‖B‖ ≤ 2 ∧
      ‖B - unit‖ ≤ 2 * (K * ((1 + |θ|) ^ Q + 1) * (L + L)) ∧
      (∀ j : activeBlocks (d := d) ℓ h, ‖symbolPart j B‖ ≤ 2 * K * (L + L) *
        ((Q : ℝ) * ((θ / 2) * ((3 / N₀) * (ℓ / (2 * r)) ^ Fintype.card d)) * (1 + θ) ^ (Q - 1))) ∧
      0 < H.weight 0 ∧
      (∀ n, H.weight (PairedSeries.flipLabel n + 1) = H.weight (n + 1)) ∧
      (∀ ζ, kernel ζ 0 = paperCoefficientLaw Q) ∧ (∀ ζ n y, 0 < (kernel ζ n).weight y) ∧
      (∀ ζ n, (∑ y, (H.joint (kernel ζ)).weight (n, y)) = H.weight n) ∧
      HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom unit
        (pairedAtom reflection (naturalPhysicalAtom (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ)) n) B ∧
      (∀ ζ (u : UnitChart (Fin Q × d)), HasSum (fun n => H.weight n *
        ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ (fun a => u.val (j, a)))
        (pointValue (torusProjection u.val)
          (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u.val (j, a))) ζ B)) ∧
      (∀ ζ i (u : UnitChart (Fin Q × d)), HasSum (fun n => (H.weight n *
        ((kernel ζ n).expect (monomialFeature (paperCoefficientAtoms Q ρ) i) -
          (paperCoefficientLaw Q).expect (monomialFeature (paperCoefficientAtoms Q ρ) i))) *
        ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ (fun a => u.val (j, a)))
        (paperPhysicalOutcomeValue Q ρ x₀ r h k c w N t τ B i u.val
          (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u.val (j, a))) ζ)) ∧
      (∀ j ∉ carrierLocalSigns x₀ ℓ r h k, symbolPart j B = 0) ∧
      ∀ ζ ζ', (∀ j ∈ carrierLocalSigns x₀ ℓ r h k, ζ j = ζ' j) → kernel ζ = kernel ζ' := by
  rcases hcarr.2.2.2 with ⟨B, H, kernel, href, hnorm, hball, hsymbol, hzero, hpair,
    hbase, hpositive, hmarginal, hseries, hdensity, hmoment⟩
  have hsupport : ∀ j ∉ carrierLocalSigns x₀ ℓ r h k, symbolPart j B = 0 :=
    physicalCarrier_series_symbol_zero x₀ ℓ r h hr k c w N θ hc H.weight B hseries
  let localKernel := fun ζ => kernel (Walsh.freezeOutside (carrierLocalSigns x₀ ℓ r h k) ζ)
  refine ⟨B, H, localKernel, href, hnorm, hball, hsymbol, hzero, hpair,
    fun ζ => hbase _, fun ζ n y => hpositive _ n y, fun ζ n => hmarginal _ n,
    hseries, hdensity, ?_, hsupport, ?_⟩
  · intro ζ i u
    let frozen := Walsh.freezeOutside (carrierLocalSigns x₀ ℓ r h k) ζ
    have he : ∀ j ∈ carrierLocalSigns x₀ ℓ r h k, frozen j = ζ j := by
      intro j hj
      simp only [frozen, Walsh.freezeOutside, if_pos hj]
    have hprod (n : ℕ) :
        (∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n frozen (fun a => u.val (j, a))) =
        ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ (fun a => u.val (j, a)) := by
      apply Finset.prod_congr rfl
      intro j _
      exact carrierPhysicalDensity_local_congr x₀ ℓ r h hr k c w N θ hc n frozen ζ he _
        ⟨fun a => u.property.1 (j, a), fun a => u.property.2 (j, a)⟩
    have htarget := physicalOutcomeTarget_local_congr Q ρ x₀ ℓ r h hr k c w N t τ
      B hsupport i u.val u.property frozen ζ he
    have hs := hmoment frozen i u
    simp_rw [hprod, htarget] at hs
    exact hs
  · intro ζ ζ' he
    exact congrArg kernel (Walsh.freezeOutside_congr (carrierLocalSigns x₀ ℓ r h k) ζ ζ' he)

end CausalLowerbound.PartC
