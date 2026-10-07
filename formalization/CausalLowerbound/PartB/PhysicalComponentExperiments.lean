import CausalLowerbound.PartB.ComponentReindex
import CausalLowerbound.PartB.ComponentCarrierRestriction
import CausalLowerbound.PartB.PhysicalFiniteExperiment

/-! The actual physical conditional experiments restrict to components.
The posterior laws are those computed from each component's own sites. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype physicalComponentFintype
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Inhabited Ω]

theorem finitePhysicalConditional_component_congr {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ) (hr : 0 < r)
    (μ ν : S → FiniteLaw Ω) {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {n m : ℕ} (x : Fin n → d → ℝ)
    (c : Option (observationGraph S x₀ r x).ConnectedComponent)
    (e : Fin m ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c})
    (hμ : ∀ k : S, blockComponent (fun j (b : S) => x j ∈ carrierBox x₀ r b.val) k = c → μ k = ν k) :
    finitePhysicalConditional side S atoms x₀ r h a b t δ μ hlegal hκ (componentConfiguration S x₀ r x c e) =
      finitePhysicalConditional side S atoms x₀ r h a b t δ ν hlegal hκ (componentConfiguration S x₀ r x c e) := by
  apply FiniteLaw.ext
  intro w
  rw [finitePhysicalConditional_weight, finitePhysicalConditional_weight]
  apply FiniteLaw.expect_independent_local μ ν
    (fun k => blockComponent (fun j (b : S) => x j ∈ carrierBox x₀ r b.val) k = c) hμ
  intro z z' hz
  apply Finset.prod_congr rfl
  intro i _
  apply modelCellMass_incident_local side S atoms x₀ r h a b t δ hr
  intro k hk
  exact hz k ((blockComponent_of_inc (fun j (b : S) => x j ∈ carrierBox x₀ r b.val)
    (e i).val k hk).trans (e i).property)

theorem finitePhysicalConditional_posterior_component {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ) (hr : 0 < r)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {n m : ℕ} (x : Fin n → d → ℝ)
    (c : Option (observationGraph S x₀ r x).ConnectedComponent)
    (e : Fin m ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c}) :
    finitePhysicalConditional side S atoms x₀ r h a b t δ
      (physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r x) hlegal hκ (componentConfiguration S x₀ r x c e) =
      finitePhysicalConditional side S atoms x₀ r h a b t δ
        (physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r (componentConfiguration S x₀ r x c e))
        hlegal hκ (componentConfiguration S x₀ r x c e) := by
  apply finitePhysicalConditional_component_congr side S atoms x₀ r h a b t δ hr
  intro k hk
  exact (physicalCoefficientPosteriors_component H kernel Q S θ hθ hθ1 x₀ r x c e k hk).symm

theorem physical_component_hellinger {Q : ℕ} (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ) (hr : 0 < r)
    (μ ν : S → FiniteLaw Ω) {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ (side : Bool) (z : S → Ω),
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {n : ℕ} (x : Fin n → d → ℝ)
    (m : Option (observationGraph S x₀ r x).ConnectedComponent → ℕ)
    (e : ∀ c, Fin (m c) ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c}) :
    (finitePhysicalConditional true S atoms x₀ r h a b t δ μ (hlegal true) hκ x).hellingerSq
      (finitePhysicalConditional false S atoms x₀ r h a b t δ ν (hlegal false) hκ x) ≤
        ∑ c, (finitePhysicalConditional true S atoms x₀ r h a b t δ μ (hlegal true) hκ
          (componentConfiguration S x₀ r x c (e c))).hellingerSq
          (finitePhysicalConditional false S atoms x₀ r h a b t δ ν (hlegal false) hκ
            (componentConfiguration S x₀ r x c (e c))) := by
  let L := fun (side : Bool) (i : Fin n) (z : S → Ω) =>
    (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).conditionalLaw
      (hlegal side z) hκ (x i)
  have hl (side : Bool) (i : Fin n) (z z' : S → Ω)
      (hz : ∀ k : S, x i ∈ carrierBox x₀ r k.val → z k = z' k) : L side i z = L side i z' := by
    apply FiniteLaw.ext
    intro w
    change (_ : FiniteLaw (Bool × Bool)).weight w = _
    rw [← modelCellMass_eq_conditional, ← modelCellMass_eq_conditional]
    exact modelCellMass_incident_local side S atoms x₀ r h a b t δ hr (x i) w z z' hz
  exact reindexed_component_hellinger μ ν (fun j (k : S) => x j ∈ carrierBox x₀ r k.val)
    (L true) (L false) (hl true) (hl false) m e

theorem physical_posterior_component_hellinger {Q : ℕ} (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (μ : S → FiniteLaw Ω)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ) (hr : 0 < r)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ (side : Bool) (z : S → Ω),
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {n : ℕ} (x : Fin n → d → ℝ)
    (m : Option (observationGraph S x₀ r x).ConnectedComponent → ℕ)
    (e : ∀ c, Fin (m c) ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c}) :
    (finitePhysicalConditional true S atoms x₀ r h a b t δ μ (hlegal true) hκ x).hellingerSq
      (finitePhysicalConditional false S atoms x₀ r h a b t δ
        (physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r x) (hlegal false) hκ x) ≤
        ∑ c, (finitePhysicalConditional true S atoms x₀ r h a b t δ μ (hlegal true) hκ
          (componentConfiguration S x₀ r x c (e c))).hellingerSq
          (finitePhysicalConditional false S atoms x₀ r h a b t δ
            (physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r (componentConfiguration S x₀ r x c (e c)))
            (hlegal false) hκ (componentConfiguration S x₀ r x c (e c))) := by
  have he := physical_component_hellinger S atoms x₀ r h a b t δ hr μ
    (physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r x) hlegal hκ x m e
  simp_rw [finitePhysicalConditional_posterior_component false S atoms H kernel θ hθ hθ1
    x₀ r h a b t δ hr (hlegal false) hκ x] at he
  exact he

end CausalLowerbound.PartB.ShellGeometry
