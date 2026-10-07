import CausalLowerbound.PartC.BlockPriorRestriction
import CausalLowerbound.PartC.RawCarrierConditional
import CausalLowerbound.PartC.PhysicalDesignLocality

/-! Marginalize unused blocks in the actual design-weighted experiment.
Both the raw observation mixture and its design normalizer are preserved,
so the resulting finite conditional laws are equal. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I J Ω : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype Ω]
  {θ : ℝ} {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

theorem rawCarrierDesignMarginal_finset_restrict
    (S T : Finset (d → ℤ)) (hTS : T ⊆ S) (x₀ : d → ℝ) (r : ℝ)
    (F : ((S → ℕ) × (J → Bool)) → CarrierProfile d θ)
    (F' : ((T → ℕ) × (J → Bool)) → CarrierProfile d θ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : S → DiscreteLaw ℕ) (x : I → d → ℝ)
    (hF : ∀ labels ζ i, (F (labels, ζ)).product S x₀ r (x i) =
      (F' ((fun k : T => labels ⟨k.val, hTS k.property⟩), ζ)).product T x₀ r (x i)) :
    rawCarrierDesignMarginal F S x₀ r H x =
      rawCarrierDesignMarginal F' T x₀ r (fun k : T => H ⟨k.val, hTS k.property⟩) x := by
  have hb (ζ : J → Bool) (labels : T → ℕ) :
      |∏ i, (F' (labels, ζ)).product T x₀ r (x i)| ≤
        ((1 + θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I := by
    have he := (F' (labels, ζ)).observation_product_bounds hθ hθ1 T x₀ r x
    rw [abs_of_nonneg ((pow_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) _).trans he.1)]
    exact he.2
  unfold rawCarrierDesignMarginal
  simp_rw [hF]
  exact sharedSignPrior_expect_finset_subset S T hTS H
    (fun ζ labels => ∏ i, (F' (labels, ζ)).product T x₀ r (x i)) _ hb

theorem rawCarrierObservationMixture_finset_restrict
    (S T : Finset (d → ℤ)) (hTS : T ⊆ S) (x₀ : d → ℝ) (r : ℝ)
    (F : ((S → ℕ) × (J → Bool)) → CarrierProfile d θ)
    (F' : ((T → ℕ) × (J → Bool)) → CarrierProfile d θ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : S → DiscreteLaw ℕ)
    (kernel : S → (J → Bool) → ℕ → FiniteLaw Ω)
    (fields : (((S → ℕ) × (J → Bool)) × (S → Ω)) → NuisanceFields d)
    (fields' : (((T → ℕ) × (J → Bool)) × (T → Ω)) → NuisanceFields d)
    (hlegal' : ∀ z, (fields' z).Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (x : I → d → ℝ)
    (hF : ∀ labels ζ i, (F (labels, ζ)).product S x₀ r (x i) =
      (F' ((fun k : T => labels ⟨k.val, hTS k.property⟩), ζ)).product T x₀ r (x i))
    (hcells : ∀ labels ζ ξ i y, nuisanceCellMass (fields ((labels, ζ), ξ)) (x i) y =
      nuisanceCellMass (fields' (((fun k : T => labels ⟨k.val, hTS k.property⟩), ζ),
        (fun k : T => ξ ⟨k.val, hTS k.property⟩))) (x i) y)
    (y : I → Bool × Bool) :
    (signBlockPrior H kernel).expect (fun z => ∏ i,
      (F z.1).product S x₀ r (x i) * nuisanceCellMass (fields z) (x i) (y i)) =
      (signBlockPrior (fun k : T => H ⟨k.val, hTS k.property⟩)
        (fun k : T => kernel ⟨k.val, hTS k.property⟩)).expect (fun z => ∏ i,
          (F' z.1).product T x₀ r (x i) * nuisanceCellMass (fields' z) (x i) (y i)) := by
  have hb (ζ : J → Bool) (labels : T → ℕ) (ξ : T → Ω) :
      |∏ i, (F' (labels, ζ)).product T x₀ r (x i) *
        nuisanceCellMass (fields' ((labels, ζ), ξ)) (x i) (y i)| ≤
          ((1 + θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : I, (1 + θ) ^ (5 ^ Fintype.card d) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ =>
          (F' (labels, ζ)).product_cellMass_bound hθ hθ1 T x₀ r _ (x i) (y i) (hlegal' _) hκ)
      _ = _ := by simp
  simp_rw [show ∀ z : ((S → ℕ) × (J → Bool)) × (S → Ω),
      (∏ i, (F z.1).product S x₀ r (x i) * nuisanceCellMass (fields z) (x i) (y i)) =
        ∏ i, (F' ((fun k : T => z.1.1 ⟨k.val, hTS k.property⟩), z.1.2)).product T x₀ r (x i) *
          nuisanceCellMass (fields' (((fun k : T => z.1.1 ⟨k.val, hTS k.property⟩), z.1.2),
            (fun k : T => z.2 ⟨k.val, hTS k.property⟩))) (x i) (y i) from by
    intro z
    apply Finset.prod_congr rfl
    intro i _
    rw [hF z.1.1 z.1.2 i, hcells z.1.1 z.1.2 z.2 i (y i)]]
  exact signBlockPrior_expect_finset_subset S T hTS H kernel
    (fun ζ labels ξ => ∏ i, (F' (labels, ζ)).product T x₀ r (x i) *
      nuisanceCellMass (fields' ((labels, ζ), ξ)) (x i) (y i)) _ hb

theorem rawCarrierConditional_finset_restrict
    (S T : Finset (d → ℤ)) (hTS : T ⊆ S) (x₀ : d → ℝ) (r : ℝ)
    (F : ((S → ℕ) × (J → Bool)) → CarrierProfile d θ)
    (F' : ((T → ℕ) × (J → Bool)) → CarrierProfile d θ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : S → DiscreteLaw ℕ)
    (kernel : S → (J → Bool) → ℕ → FiniteLaw Ω)
    (fields : (((S → ℕ) × (J → Bool)) × (S → Ω)) → NuisanceFields d)
    (fields' : (((T → ℕ) × (J → Bool)) × (T → Ω)) → NuisanceFields d)
    (hlegal : ∀ z, (fields z).Legal α β γ Lπ L₀ Lτ κ)
    (hlegal' : ∀ z, (fields' z).Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (x : I → d → ℝ)
    (hF : ∀ labels ζ i, (F (labels, ζ)).product S x₀ r (x i) =
      (F' ((fun k : T => labels ⟨k.val, hTS k.property⟩), ζ)).product T x₀ r (x i))
    (hcells : ∀ labels ζ ξ i y, nuisanceCellMass (fields ((labels, ζ), ξ)) (x i) y =
      nuisanceCellMass (fields' (((fun k : T => labels ⟨k.val, hTS k.property⟩), ζ),
        (fun k : T => ξ ⟨k.val, hTS k.property⟩))) (x i) y) :
    rawCarrierConditional F hθ hθ1 S x₀ r H kernel fields hlegal hκ x =
      rawCarrierConditional F' hθ hθ1 T x₀ r (fun k : T => H ⟨k.val, hTS k.property⟩)
        (fun k : T => kernel ⟨k.val, hTS k.property⟩) fields' hlegal' hκ x := by
  apply FiniteLaw.ext
  intro y
  rw [rawCarrierConditional_weight, rawCarrierConditional_weight,
    rawCarrierObservationMixture_finset_restrict S T hTS x₀ r F F' hθ hθ1 H kernel
      fields fields' hlegal' hκ x hF hcells y,
    rawCarrierDesignMarginal_finset_restrict S T hTS x₀ r F F' hθ hθ1 H x hF]

end CausalLowerbound.PartC
