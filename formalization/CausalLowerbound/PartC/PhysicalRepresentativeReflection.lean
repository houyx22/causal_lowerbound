import CausalLowerbound.PartC.PhysicalRepresentativeEvaluation
import CausalLowerbound.PartC.RepresentativeReflection

/-! The formal reflection is the actual global sign flip after evaluation
on physical rough packets, including the normalized carrier multiplier. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Representative

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem physicalRoughField_flip (x₀ : d → ℝ) (ℓ h : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) :
    physicalRoughField x₀ ℓ h (Walsh.flip ζ) x = -physicalRoughField x₀ ℓ h ζ x := by
  have hs (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num [sign]
  simp only [physicalRoughField_eq_sum, Walsh.flip, hs, mul_neg, Finset.sum_neg_distrib]

theorem normalizedRoughChart_flip (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    normalizedRoughChart x₀ ℓ r h k c w N (Walsh.flip ζ) u =
      -normalizedRoughChart x₀ ℓ r h k c w N ζ u := by
  simp only [normalizedRoughChart, physicalRoughField_flip, mul_neg, neg_div]

theorem physical_pointValue_reflection (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : (ι × d) → ℝ)
    (a : Array d ι (activeBlocks (d := d) ℓ h) D) :
    pointValue (Wiener.torusProjection u)
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u (i, j))) ζ (reflection a) =
    pointValue (Wiener.torusProjection u)
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N (Walsh.flip ζ) (fun j => u (i, j))) (Walsh.flip ζ) a := by
  rw [pointValue_reflection]
  simp only [normalizedRoughChart_flip]

theorem physical_pointValue_evenPart (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : (ι × d) → ℝ)
    (a : Array d ι (activeBlocks (d := d) ℓ h) D) :
    pointValue (Wiener.torusProjection u)
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N (Walsh.flip ζ) (fun j => u (i, j)))
      (Walsh.flip ζ) (evenPart a) =
    pointValue (Wiener.torusProjection u)
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u (i, j))) ζ (evenPart a) := by
  rw [← physical_pointValue_reflection, reflection_evenPart]

end CausalLowerbound.PartC
