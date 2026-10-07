import CausalLowerbound.PartC.MixedModels
import CausalLowerbound.PartC.SharedCarrierGeometry
import CausalLowerbound.PartC.SharedObservationFactorization
import CausalLowerbound.PartB.LegalBinaryModels

/-! Locality of the actual binary cell probabilities in both mixed
models. The smooth carried field and the rough sign field are checked
separately against the enlarged observation incidence graph. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d V Ω : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype Ω] [Inhabited Ω]

theorem carriedField_incident_local {Q : ℕ} (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (x : d → ℝ) (u v : S → Ω)
    (he : ∀ k : S, x ∈ carrierBox x₀ r k.val → u k = v k) :
    carriedField S (fun k => atoms (extendBlockSample S u k)) x₀ r x =
      carriedField S (fun k => atoms (extendBlockSample S v k)) x₀ r x := by
  rw [carriedField_eq_physical _ _ _ _ hr, carriedField_eq_physical _ _ _ _ hr]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hx : x ∈ carrierBox x₀ r k
  · simp only [extendBlockSample, dif_pos hk, he ⟨k, hk⟩ hx]
  · have hz : linearPartition (fun a => (x a - x₀ a) / r - k a) = 0 := by
      by_contra hn
      have hb := linearPartition_support (subset_tsupport _ hn)
      apply hx
      exact ⟨fun a => (by norm_num : (-2 : ℝ) ≤ -1).trans (hb.1 a),
        fun a => (hb.2 a).trans (by norm_num : (1 : ℝ) ≤ 2)⟩
    rw [hz, zero_mul, zero_mul]

def nuisanceCellMass (F : NuisanceFields d) (x : d → ℝ) (y : Bool × Bool) : ℝ :=
  codedLikelihood (sign y.1) (sign y.2)
    (2 * F.propensity x - 1) (2 * F.baseline x - 1) (F.effect x) / 4

theorem nuisanceCellMass_eq_conditional (F : NuisanceFields d) (x : d → ℝ) (y : Bool × Bool)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ} (hlegal : F.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ) :
    nuisanceCellMass F x y = (F.conditionalLaw hlegal hκ x).weight y := rfl

theorem nuisanceCellMass_abs_le_one (F : NuisanceFields d) (x : d → ℝ) (y : Bool × Bool)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ} (hlegal : F.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ) :
    |nuisanceCellMass F x y| ≤ 1 := by
  rw [nuisanceCellMass_eq_conditional F x y hlegal hκ,
    abs_of_nonneg ((F.conditionalLaw hlegal hκ x).nonneg y)]
  exact (F.conditionalLaw hlegal hκ x).weight_le_one y

theorem roughPropensity_cell_local_congr {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (hr : 0 < r)
    (x : d → ℝ) (y : Bool × Bool) (u v : S → Ω)
    (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (hu : ∀ k : S, x ∈ carrierBox x₀ r k.val → u k = v k)
    (hζ : ∀ j ∈ physicalLocalSigns x₀ ℓ h x, ζ j = ζ' j) :
    nuisanceCellMass (roughPropensityFields side S (fun k => atoms (extendBlockSample S u k))
      x₀ ℓ r h ja b t ζ) x y =
    nuisanceCellMass (roughPropensityFields side S (fun k => atoms (extendBlockSample S v k))
      x₀ ℓ r h ja b t ζ') x y := by
  unfold nuisanceCellMass
  rw [roughPropensityFields_likelihood, roughPropensityFields_likelihood,
    carriedField_incident_local S atoms x₀ r hr x u v hu,
    physicalRoughField_local_congr x₀ ℓ h x ζ ζ' hζ]

theorem roughOutcome_cell_local_congr {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (hr : 0 < r)
    (x : d → ℝ) (y : Bool × Bool) (u v : S → Ω)
    (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (hu : ∀ k : S, x ∈ carrierBox x₀ r k.val → u k = v k)
    (hζ : ∀ j ∈ physicalLocalSigns x₀ ℓ h x, ζ j = ζ' j) :
    nuisanceCellMass (roughOutcomeFields side S (fun k => atoms (extendBlockSample S u k))
      x₀ ℓ r h a jb t ζ) x y =
    nuisanceCellMass (roughOutcomeFields side S (fun k => atoms (extendBlockSample S v k))
      x₀ ℓ r h a jb t ζ') x y := by
  unfold nuisanceCellMass
  rw [roughOutcomeFields_likelihood, roughOutcomeFields_likelihood,
    carriedField_incident_local S atoms x₀ r hr x u v hu,
    physicalRoughField_local_congr x₀ ℓ h x ζ ζ' hζ]

theorem roughPropensity_observation_local {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (hr : 0 < r)
    (x : V → d → ℝ) (y : V → Bool × Bool) :
    SharedObservationLocal (physicalSharedIncidence S x₀ ℓ r h x)
      (fun i ζ _ u => nuisanceCellMass (roughPropensityFields side S
        (fun k => atoms (extendBlockSample S u k)) x₀ ℓ r h ja b t ζ) (x i) (y i)) := by
  intro i ζ ζ' _ _ u v hζ _ hu
  exact roughPropensity_cell_local_congr side S atoms x₀ ℓ r h ja b t hr (x i) (y i) u v ζ ζ'
    hu (fun j hj => hζ j (Or.inl hj))

theorem roughOutcome_observation_local {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (hr : 0 < r)
    (x : V → d → ℝ) (y : V → Bool × Bool) :
    SharedObservationLocal (physicalSharedIncidence S x₀ ℓ r h x)
      (fun i ζ _ u => nuisanceCellMass (roughOutcomeFields side S
        (fun k => atoms (extendBlockSample S u k)) x₀ ℓ r h a jb t ζ) (x i) (y i)) := by
  intro i ζ ζ' _ _ u v hζ _ hu
  exact roughOutcome_cell_local_congr side S atoms x₀ ℓ r h a jb t hr (x i) (y i) u v ζ ζ'
    hu (fun j hj => hζ j (Or.inl hj))

end CausalLowerbound.PartC
