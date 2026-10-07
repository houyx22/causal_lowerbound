import CausalLowerbound.PartC.PhysicalDesignLocality
import CausalLowerbound.PartC.DensityCarrierMarginals

/-! Regroup the actual sample design by carrier blocks. Only observations
inside a block enter its retained tensor; all other factors are exactly one.
Every retained configuration of at most Q sites has a Q-slot completion. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I]

theorem CarrierProfile.factor_product_retained {θ : ℝ} (F : CarrierProfile d θ)
    (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (x : I → d → ℝ) :
    (∏ i, F.factor x₀ r k (x i)) =
      ∏ i : {i // x i ∈ carrierBox x₀ r k},
        F.density k (carrierCoordinate (localCoordinate x₀ r k (x i.val))) := by
  let S := Finset.univ.filter (fun i => x i ∈ carrierBox x₀ r k)
  calc
    _ = ∏ i ∈ S, F.density k (carrierCoordinate (localCoordinate x₀ r k (x i))) := by
      simp only [S, Finset.prod_filter, CarrierProfile.factor]
    _ = _ := Finset.prod_subtype S (fun i => by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]) _

theorem CarrierProfile.sample_product_retained {θ : ℝ} (F : CarrierProfile d θ)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (x : I → d → ℝ) :
    (∏ i, F.product S x₀ r (x i)) =
      ∏ k : S, ∏ i : {i // x i ∈ carrierBox x₀ r k.val},
        F.density k.val (carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) := by
  have hf (i : I) : F.product S x₀ r (x i) = ∏ k : S, F.factor x₀ r k.val (x i) :=
    (Finset.prod_coe_sort S (fun k => F.factor x₀ r k (x i))).symm
  simp_rw [hf]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro k _
  exact F.factor_product_retained x₀ r k.val x

theorem retained_design_chart_mem_cube (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ)
    (x : I → d → ℝ) (i : {i // x i ∈ carrierBox x₀ r k}) :
    carrierCoordinate (localCoordinate x₀ r k (x i.val)) ∈ Set.Icc (0 : d → ℝ) 1 :=
  carrierCoordinate_mem_cube x₀ r k (x i.val) i.property

theorem retained_design_card_le (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (x : I → d → ℝ) :
    Fintype.card {i // x i ∈ carrierBox x₀ r k} ≤ Fintype.card I :=
  Fintype.card_le_of_injective _ Subtype.val_injective

def retainedDesignCompletion (Q : ℕ) (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ)
    (x : I → d → ℝ) (hQ : Fintype.card I ≤ Q) :
    {i // x i ∈ carrierBox x₀ r k} ⊕
      Fin (Q - Fintype.card {i // x i ∈ carrierBox x₀ r k}) ≃ Fin Q :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_fin]
    have hs := (retained_design_card_le x₀ r k x).trans hQ
    omega)

end CausalLowerbound.PartC
