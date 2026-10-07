import CausalLowerbound.PartC.PropensityMomentWitness

/-! Choose actual local carrier witnesses with a uniform geometric
symbol bound. Once the vanishing carrier error is at most one, the
coefficient depends only on fixed moment and carrier constants. -/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def propensityWitnessSymbolConstant (d : Type*) [Fintype d] [DecidableEq d]
    (Q : ℕ) (N₀ θ K : ℝ) : ℝ :=
  let P := (Fintype.card (MomentExponent (CoefficientExponent d Q) (4 * Q)) : ℝ) *
    polarizationBound (Fin Q) θ
  2 * K * (P + P) * ((Q : ℝ) * ((θ / 2) * (1 / N₀)) * (1 + θ) ^ (Q - 1))

theorem propensityWitnessSymbolConstant_nonneg (Q : ℕ) (N₀ θ K : ℝ)
    (hN₀ : 0 < N₀) (hθ : 0 ≤ θ) (hK : 0 ≤ K) :
    0 ≤ propensityWitnessSymbolConstant d Q N₀ θ K := by
  have hP := polarizationBound_nonneg (ι := Fin Q) θ
  unfold propensityWitnessSymbolConstant
  positivity

theorem exists_boundedPropensityMomentWitness
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 ≤ ℓ) (hr : 0 < r) (k : d → ℤ)
    (c w N N₀ θ ja t τ K δ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hδ : δ ≤ 1) (hcarr : HasPaperPropensityCarrier Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ) :
    ∃ R : PropensityMomentWitness Q ρ x₀ ℓ r h k c w N θ ja t τ,
      ∀ j, ‖symbolPart j R.representative‖ ≤
        propensityWitnessSymbolConstant d Q N₀ θ K * (ℓ / (2 * r)) ^ Fintype.card d := by
  obtain ⟨R, _, hR⟩ := exists_localPropensityMomentWitness Q ρ x₀ ℓ r h hr.ne' k
    c w N N₀ θ ja t τ K δ hc hcarr
  refine ⟨R, fun j => ?_⟩
  have hraw : ‖symbolPart j R.representative‖ ≤
      (propensityWitnessSymbolConstant d Q N₀ θ K * (ℓ / (2 * r)) ^ Fintype.card d) * δ := by
    apply (hR j).trans_eq
    dsimp only [propensityWitnessSymbolConstant]
    ring
  exact hraw.trans (mul_le_of_le_one_right
    (mul_nonneg (propensityWitnessSymbolConstant_nonneg Q N₀ θ K hN₀ hθ hK)
      (pow_nonneg (div_nonneg hℓ (by positivity)) _)) hδ)

theorem exists_boundedPropensityMomentWitness_family
    (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 ≤ ℓ) (hr : 0 < r)
    (c w N N₀ θ ja t τ K δ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hδ : δ ≤ 1) (hcarr : ∀ k : S, HasPaperPropensityCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ ja t τ K δ) :
    ∃ R : ∀ k : S, PropensityMomentWitness Q ρ x₀ ℓ r h k.val c w N θ ja t τ,
      ∀ k j, ‖symbolPart j (R k).representative‖ ≤
        propensityWitnessSymbolConstant d Q N₀ θ K * (ℓ / (2 * r)) ^ Fintype.card d := by
  have hex (k : S) := exists_boundedPropensityMomentWitness Q ρ x₀ ℓ r h hℓ hr k.val
    c w N N₀ θ ja t τ K δ hc hN₀ hθ hK hδ (hcarr k)
  choose R hR using hex
  exact ⟨R, hR⟩

end CausalLowerbound.PartC
