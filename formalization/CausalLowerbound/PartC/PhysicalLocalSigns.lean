import CausalLowerbound.PartC.LocalSignResampling
import CausalLowerbound.PartC.PhysicalRoughMoments

/-! Actual local sign sets of the physical rough field. Separated sites
use disjoint sets, and fresh-copy replacement follows from finite product
weights rather than an independence premise on the physical fields. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]

def physicalLocalSigns (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ) :
    Finset (activeBlocks (d := d) ℓ h) :=
  Finset.univ.filter (fun k => packet (coarseBump x₀ h) x₀ ℓ k.val x ≠ 0)

theorem physicalRoughField_local_congr (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ)
    (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (hζ : ∀ j ∈ physicalLocalSigns x₀ ℓ h x, ζ j = ζ' j) :
    physicalRoughField x₀ ℓ h ζ x = physicalRoughField x₀ ℓ h ζ' x := by
  rw [physicalRoughField_eq_sum, physicalRoughField_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : packet (coarseBump x₀ h) x₀ ℓ j.val x = 0
  · simp only [hj, zero_mul]
  · rw [hζ j (by simp only [physicalLocalSigns, Finset.mem_filter, Finset.mem_univ, true_and]; exact hj)]

theorem physicalLocalSigns_disjoint (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ)
    (x y : d → ℝ) (hxy : 2 * ℓ < ‖x - y‖) :
    Disjoint (physicalLocalSigns x₀ ℓ h x) (physicalLocalSigns x₀ ℓ h y) := by
  apply Finset.disjoint_left.mpr
  intro j hx hy
  simp only [physicalLocalSigns, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact (not_le_of_gt hxy) (packet_common_support_distance (coarseBump x₀ h) x₀ ℓ hℓ j.val x y hx hy)

theorem physicalLocalSigns_card (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ) :
    (physicalLocalSigns x₀ ℓ h x).card ≤ 2 ^ Fintype.card d := by
  have hs : (physicalLocalSigns x₀ ℓ h x).image Subtype.val ⊆
      latticeNeighbors (fun i => (x i - x₀ i) / ℓ) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hn : packet (coarseBump x₀ h) x₀ ℓ j.val x ≠ 0 := by
      simpa only [physicalLocalSigns, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    by_contra hout
    apply hn
    simp only [packet, quadraticPartition_zero_outside_neighbors _ _ hout, mul_zero]
  have hb := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ Subtype.val_injective, latticeNeighbors_card] at hb
  exact hb

theorem physicalRoughField_resampling (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) (x : V → d → ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (g : (activeBlocks (d := d) ℓ h → Bool) → (V → ℝ) → ℝ)
    (hg : ∀ ζ ζ' v, (∀ j, (∀ i, j ∉ physicalLocalSigns x₀ ℓ h (x i)) → ζ j = ζ' j) →
      g ζ v = g ζ' v) :
    independentSigns.expect (fun ζ => g ζ (fun i => physicalRoughField x₀ ℓ h ζ (x i))) =
      independentSigns.expect (fun base =>
        (FiniteLaw.independent (fun _ : V => independentSigns (ι := activeBlocks (d := d) ℓ h))).expect
          (fun fresh => g base (fun i => physicalRoughField x₀ ℓ h (fresh i) (x i)))) := by
  apply disjoint_sign_resampling (fun i => physicalLocalSigns x₀ ℓ h (x i))
    (fun i j hij => physicalLocalSigns_disjoint x₀ ℓ h hℓ (x i) (x j) (hsep i j hij))
  · intro i ζ ζ' he
    exact physicalRoughField_local_congr x₀ ℓ h (x i) ζ ζ' he
  · exact hg

end CausalLowerbound.PartC
