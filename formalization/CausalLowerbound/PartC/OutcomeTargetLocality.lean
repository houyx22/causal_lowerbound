import CausalLowerbound.PartC.PhysicalOutcomeTarget
import CausalLowerbound.PartC.CarrierLocalSigns
import CausalLowerbound.PartC.RepresentativeLocality

/-! The prescribed outcome increment inherits the explicit symbol
support of its representative. The rough variables are localized separately. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt

variable {Ω K V E d J : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype d] [DecidableEq d]
  [Fintype J] [DecidableEq J]

theorem outcomeChoiceValue_local_congr (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (amp t : ℝ) (κ : V → ℝ) (v : Representative.Array d V J 3)
    (T : Finset J) (hv : ∀ j ∉ T, symbolPart j v = 0)
    (u : V × d → ℝ) (z : V → ℝ) (ζ ζ' : J → Bool)
    (hζ : ∀ j ∈ T, ζ j = ζ' j) :
    outcomeChoiceValue a b μ U ν amp t κ v u z ζ =
      outcomeChoiceValue a b μ U ν amp t κ v u z ζ' := by
  unfold outcomeChoiceValue
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [character_coefficient_local_congr T v hv r (torusProjection u) ζ ζ' hζ]
  · rfl

theorem paperPhysicalOutcomeValue_local_congr (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ)
    (r h : ℝ) (k : d → ℤ) (c w N t τ : ℝ) (v : Representative.Array d (Fin Q) J 3)
    (T : Finset J) (hv : ∀ j ∉ T, symbolPart j v = 0)
    (η : MomentExponent (CoefficientExponent d Q) (4 * Q))
    (u : Fin Q × d → ℝ) (z : Fin Q → ℝ) (ζ ζ' : J → Bool)
    (hζ : ∀ j ∈ T, ζ j = ζ' j) :
    paperPhysicalOutcomeValue Q ρ x₀ r h k c w N t τ v η u z ζ =
      paperPhysicalOutcomeValue Q ρ x₀ r h k c w N t τ v η u z ζ' := by
  unfold paperPhysicalOutcomeValue
  apply congrArg (fun s : ℝ => (Fintype.card (Equiv.Perm (Fin Q)) : ℝ)⁻¹ * s)
  apply Finset.sum_congr rfl
  intro σ _
  exact outcomeChoiceValue_local_congr edgeLeft edgeRight (paperCoefficientLaw Q)
    (fun ω (j : MomentPositions η) => paperCoefficientAtoms Q ρ ω j.1)
    (fun j : MomentPositions η => polynomialBasisDegree j.1) (t * N) τ
    (fun i => normalizedRoughVariance x₀ r h k c w N (fun j => u (σ i, j)))
    v T hv (fun p => u (σ p.1, p.2)) (fun i => z (σ i)) ζ ζ' hζ

theorem physicalOutcomeTarget_local_congr (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ)
    (ℓ r h : ℝ) (hr : r ≠ 0) (k : d → ℤ) (c w N t τ : ℝ)
    (v : Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hv : ∀ j ∉ carrierLocalSigns x₀ ℓ r h k, symbolPart j v = 0)
    (η : MomentExponent (CoefficientExponent d Q) (4 * Q))
    (u : Fin Q × d → ℝ) (hu : u ∈ Set.Icc (0 : Fin Q × d → ℝ) 1)
    (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (hζ : ∀ j ∈ carrierLocalSigns x₀ ℓ r h k, ζ j = ζ' j) :
    paperPhysicalOutcomeValue Q ρ x₀ r h k c w N t τ v η u
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u (i, a))) ζ =
    paperPhysicalOutcomeValue Q ρ x₀ r h k c w N t τ v η u
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ' (fun a => u (i, a))) ζ' := by
  have hz : (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u (i, a))) =
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ' (fun a => u (i, a))) := by
    funext i
    exact normalizedRoughChart_local_congr x₀ ℓ r h hr k c w N ζ ζ' hζ _
      ⟨fun a => hu.1 (i, a), fun a => hu.2 (i, a)⟩
  rw [hz]
  exact paperPhysicalOutcomeValue_local_congr Q ρ x₀ r h k c w N t τ v
    (carrierLocalSigns x₀ ℓ r h k) hv η u _ ζ ζ' hζ

end CausalLowerbound.PartC
