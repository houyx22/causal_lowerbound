import CausalLowerbound.PartC.SharedComponentMarginals
import CausalLowerbound.PartC.RawCarrierConditional
import CausalLowerbound.PartC.PhysicalDesignLocality
import CausalLowerbound.PartB.ComponentHellinger

/-! Normalize the actual shared-sign component factorization. The design
normalizer factors along the same graph as the raw observation mixture,
giving a product of genuine conditional laws and Hellinger subadditivity. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype
variable {d I K J Ω : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω] [Inhabited Ω]
  {θ : ℝ} {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

theorem rawCarrierDesignMarginal_eq_prior
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (x : I → d → ℝ) :
    rawCarrierDesignMarginal F S x₀ r H x =
      (signBlockPrior H kernel).expect (fun z => ∏ i, (F z.1).product S x₀ r (x i)) := by
  have hb (z : (K → ℕ) × (J → Bool)) :
      |∏ i, (F z).product S x₀ r (x i)| ≤ ((1 + θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I := by
    have he := (F z).observation_product_bounds hθ hθ1 S x₀ r x
    rw [abs_of_nonneg ((pow_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) _).trans he.1)]
    exact he.2
  exact (DiscreteLaw.joint_expect_label (sharedSignPrior H) (signBlockKernel kernel)
    (fun z => ∏ i, (F z).product S x₀ r (x i)) _ hb).symm

theorem rawCarrierDesignMarginal_component_factorization
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (x : I → d → ℝ)
    (blockInc : I → K → Prop) (siteSigns : I → Finset J) (blockSigns : K → Finset J)
    (hkernel : ∀ k ζ ζ' n, (∀ j ∈ blockSigns k, ζ j = ζ' j) → kernel k ζ n = kernel k ζ' n)
    (hdesign : SharedObservationLocal (sharedSignIncidence blockInc siteSigns blockSigns)
      (fun i ζ labels (_ : K → Ω) => (F (labels, ζ)).product S x₀ r (x i))) :
    let inc := sharedSignIncidence blockInc siteSigns blockSigns
    rawCarrierDesignMarginal F S x₀ r H x =
      ∏ c : Option (incidenceGraph inc).ConnectedComponent,
        rawCarrierDesignMarginal F S x₀ r H (fun i : {i // siteComponent inc i = c} => x i.val) := by
  have hb (i : I) (ζ : J → Bool) (labels : K → ℕ) (_ : K → Ω) :
      |(F (labels, ζ)).product S x₀ r (x i)| ≤ (1 + θ) ^ (5 ^ Fintype.card d) := by
    have he := (F (labels, ζ)).product_bounds hθ hθ1 S x₀ r (x i)
    rw [abs_of_nonneg ((pow_nonneg (sub_nonneg.mpr hθ1.le) _).trans he.1)]
    exact he.2
  have he := shared_observation_factorization_marginals H kernel blockInc siteSigns blockSigns hkernel
    (fun i ζ labels (_ : K → Ω) => (F (labels, ζ)).product S x₀ r (x i))
    hdesign ((1 + θ) ^ (5 ^ Fintype.card d)) hb
  simpa only [← rawCarrierDesignMarginal_eq_prior F hθ hθ1 S x₀ r H kernel] using he

theorem rawCarrierConditional_component_factorization
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (fields : (((K → ℕ) × (J → Bool)) × (K → Ω)) → NuisanceFields d)
    (hlegal : ∀ z, (fields z).Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (x : I → d → ℝ)
    (blockInc : I → K → Prop) (siteSigns : I → Finset J) (blockSigns : K → Finset J)
    (hkernel : ∀ k ζ ζ' n, (∀ j ∈ blockSigns k, ζ j = ζ' j) → kernel k ζ n = kernel k ζ' n)
    (hdesign : SharedObservationLocal (sharedSignIncidence blockInc siteSigns blockSigns)
      (fun i ζ labels (_ : K → Ω) => (F (labels, ζ)).product S x₀ r (x i)))
    (hcell : ∀ y : I → Bool × Bool,
      SharedObservationLocal (sharedSignIncidence blockInc siteSigns blockSigns)
        (fun i ζ labels ξ => nuisanceCellMass (fields ((labels, ζ), ξ)) (x i) (y i)))
    (y : I → Bool × Bool) :
    let inc := sharedSignIncidence blockInc siteSigns blockSigns
    (rawCarrierConditional F hθ hθ1 S x₀ r H kernel fields hlegal hκ x).weight y =
      ∏ c : Option (incidenceGraph inc).ConnectedComponent,
        (rawCarrierConditional F hθ hθ1 S x₀ r H kernel fields hlegal hκ
          (fun i : {i // siteComponent inc i = c} => x i.val)).weight (fun i => y i.val) := by
  let inc := sharedSignIncidence blockInc siteSigns blockSigns
  let design := fun i ζ labels (_ : K → Ω) => (F (labels, ζ)).product S x₀ r (x i)
  let cell := fun i ζ labels ξ => nuisanceCellMass (fields ((labels, ζ), ξ)) (x i) (y i)
  have hf := SharedObservationLocal.mul inc design cell hdesign (hcell y)
  have hb (i : I) (ζ : J → Bool) (labels : K → ℕ) (ξ : K → Ω) :
      |design i ζ labels ξ * cell i ζ labels ξ| ≤ (1 + θ) ^ (5 ^ Fintype.card d) :=
    (F (labels, ζ)).product_cellMass_bound hθ hθ1 S x₀ r _ (x i) (y i) (hlegal _) hκ
  have he := shared_observation_factorization_marginals H kernel blockInc siteSigns blockSigns hkernel
    (fun i ζ labels ξ => design i ζ labels ξ * cell i ζ labels ξ) hf
    ((1 + θ) ^ (5 ^ Fintype.card d)) hb
  dsimp only [design, cell] at he
  dsimp only
  rw [rawCarrierConditional_weight, he,
    rawCarrierDesignMarginal_component_factorization F hθ hθ1 S x₀ r H kernel x
      blockInc siteSigns blockSigns hkernel hdesign, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro c _
  exact (rawCarrierConditional_weight F hθ hθ1 S x₀ r H kernel fields hlegal hκ
    (fun i : {i // siteComponent inc i = c} => x i.val) (fun i => y i.val)).symm

theorem rawCarrierConditional_component_hellinger
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : Bool → K → (J → Bool) → ℕ → FiniteLaw Ω)
    (fields : Bool → (((K → ℕ) × (J → Bool)) × (K → Ω)) → NuisanceFields d)
    (hlegal : ∀ side z, (fields side z).Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (x : I → d → ℝ)
    (blockInc : I → K → Prop) (siteSigns : I → Finset J) (blockSigns : K → Finset J)
    (hkernel : ∀ side k ζ ζ' n, (∀ j ∈ blockSigns k, ζ j = ζ' j) → kernel side k ζ n = kernel side k ζ' n)
    (hdesign : SharedObservationLocal (sharedSignIncidence blockInc siteSigns blockSigns)
      (fun i ζ labels (_ : K → Ω) => (F (labels, ζ)).product S x₀ r (x i)))
    (hcell : ∀ side (y : I → Bool × Bool),
      SharedObservationLocal (sharedSignIncidence blockInc siteSigns blockSigns)
        (fun i ζ labels ξ => nuisanceCellMass (fields side ((labels, ζ), ξ)) (x i) (y i))) :
    let inc := sharedSignIncidence blockInc siteSigns blockSigns
    let P := fun side => rawCarrierConditional F hθ hθ1 S x₀ r H (kernel side) (fields side) (hlegal side) hκ x
    (P false).hellingerSq (P true) ≤
      ∑ c : Option (incidenceGraph inc).ConnectedComponent,
        (rawCarrierConditional F hθ hθ1 S x₀ r H (kernel false) (fields false) (hlegal false) hκ
          (fun i : {i // siteComponent inc i = c} => x i.val)).hellingerSq
        (rawCarrierConditional F hθ hθ1 S x₀ r H (kernel true) (fields true) (hlegal true) hκ
          (fun i : {i // siteComponent inc i = c} => x i.val)) := by
  exact FiniteLaw.hellingerSq_fiber_factorization_le
    (siteComponent (sharedSignIncidence blockInc siteSigns blockSigns)) _ _ _ _
    (rawCarrierConditional_component_factorization F hθ hθ1 S x₀ r H (kernel false) (fields false)
      (hlegal false) hκ x blockInc siteSigns blockSigns (hkernel false) hdesign (hcell false))
    (rawCarrierConditional_component_factorization F hθ hθ1 S x₀ r H (kernel true) (fields true)
      (hlegal true) hκ x blockInc siteSigns blockSigns (hkernel true) hdesign (hcell true))

end CausalLowerbound.PartC
