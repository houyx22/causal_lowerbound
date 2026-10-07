import CausalLowerbound.PartC.CrossBlockPatternRemoval
import CausalLowerbound.PartC.PhysicalPatternBounds
import CausalLowerbound.PartC.PhysicalRepresentativeReflection

/-! The cross-block pattern-removal estimate instantiated with actual
physical corrections, normalized rough variables, and affine rough
likelihood factors. Its constant is independent of N and all physical
scales. Only the carrier's norm, reflection, and symbol estimates remain
as inputs, exactly as supplied by the constructed carrier. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
variable {d V K P I : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype K] [Fintype P] [DecidableEq P] [Fintype I]

def physicalPropensityPatternProduct (x₀ : d → ℝ) (ℓ h : ℝ) (r : K → ℝ) (k : K → d → ℤ)
    (c w N ja : ℝ) (W : K → Array d V (activeBlocks (d := d) ℓ h) 1)
    (u : K → V × d → ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool) (A : K → Finset V) : ℝ :=
  propensityPatternProduct N (fun a => physicalPropensitySlotCorrection x₀ (r a) h (k a) c w N ja (u a))
    W u (fun a i => normalizedRoughChart x₀ ℓ (r a) h (k a) c w N ζ (configurationSite (u a) i)) ζ A

set_option maxHeartbeats 500000 in
theorem physical_propensity_pattern_shift_removal_bound (x₀ : d → ℝ) (ℓ h : ℝ)
    (r : K → ℝ) (k : K → d → ℤ) (c w N N₀ ja shift η : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hfield : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hshift : 0 ≤ shift) (hsja : shift ≤ ja)
    (hη : 0 ≤ η) (sites : P → d → ℝ) (y : I → d → ℝ) (R : I → ℝ) (hR : ∀ i, |R i| ≤ 1)
    (W : K → Array d V (activeBlocks (d := d) ℓ h) 1) (u : K → V × d → ℝ)
    (A : K → Finset V) (hA : 0 < ∑ a, (A a).card)
    (hW : ∀ a, ‖W a‖ ≤ 2) (hreflect : ∀ a, reflection (W a) = W a)
    (hsymbol : ∀ a j, ‖symbolPart j (W a)‖ ≤ η) :
    let C := 1 + N₀ / c + 1 / (c * N₀)
    let S := Finset.univ.biUnion (fun p => physicalLocalSigns x₀ ℓ h (sites p))
    |independentSigns.expect (fun ζ => shift ^ (∑ a, (A a).card) *
      (physicalPropensityPatternProduct x₀ ℓ h r k c w N ja W u ζ A -
        physicalPropensityPatternProduct x₀ ℓ h r k c w N ja (fun a => remove S (W a)) u ζ A) *
          ∏ i, (1 + R i * ja * physicalRoughField x₀ ℓ h ζ (y i)))| ≤
      ((2 * C ^ Fintype.card V) ^ Fintype.card K * C ^ Fintype.card V * Fintype.card K *
        ((Fintype.card P : ℝ) * 2 ^ Fintype.card d * η)) * (2 : ℝ) ^ Fintype.card I *
          ((Fintype.card I : ℝ) + 1) * (shift * (ja * (1 + N₀))) := by
  let C := 1 + N₀ / c + 1 / (c * N₀)
  have hb₁ : 0 ≤ N₀ / c := by positivity
  have hb₂ : 0 ≤ 1 / (c * N₀) := by positivity
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hja' : ja ≤ ja * (1 + N₀) := le_mul_of_one_le_right hja (by linarith)
  have hja1 : ja ≤ 1 := hja'.trans hsmall
  have hja2 : ja ^ 2 ≤ 1 := pow_le_one₀ hja hja1
  let κ := fun a => physicalPropensitySlotCorrection x₀ (r a) h (k a) c w N ja (u a)
  let z := fun ζ a i => normalizedRoughChart x₀ ℓ (r a) h (k a) c w N ζ (configurationSite (u a) i)
  have hz (ζ) (a : K) (i : V) : |z ζ a i| ≤ 1 :=
    normalizedRoughChart_bound x₀ ℓ (r a) h (k a) c w N N₀ hc hN₀ hN hm hfield ζ _
  have hNz (ζ) (a : K) (i : V) : |N * z ζ a i| ≤ C := by
    apply (normalizedRoughChart_scaled_bound x₀ ℓ (r a) h (k a) c w N N₀ hc hN₀ hN hm hfield ζ _).trans
    dsimp only [C]
    linarith
  have hNκ (a : K) (i : V) : |N * κ a i| ≤ C := by
    apply (physicalPropensityCorrection_scaled_bound x₀ (r a) h (k a) c w N N₀ ja hc hN₀ hN hm hja2 (u a) i).trans
    dsimp only [C]
    linarith
  have hflip (ζ) (a : K) (i : V) : z (Walsh.flip ζ) a i = -z ζ a i :=
    normalizedRoughChart_flip x₀ ℓ (r a) h (k a) c w N ζ _
  have hf (i : I) (ζ) : |R i * ja * physicalRoughField x₀ ℓ h ζ (y i)| ≤ ja * (1 + N₀) := by
    have hrough : |physicalRoughField x₀ ℓ h ζ (y i)| ≤ N₀ := by
      rw [← physicalRoughWalsh_evaluate]
      exact (Walsh.evaluate_bound ζ _).trans (hfield _)
    rw [abs_mul, abs_mul, abs_of_nonneg hja]
    calc
      _ ≤ (1 * ja) * N₀ := mul_le_mul (mul_le_mul_of_nonneg_right (hR i) hja) hrough
        (abs_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith
  have he := physical_pattern_shift_removal_bound N κ x₀ ℓ h sites W u z A hA C η shift
    (ja * (1 + N₀)) hC hη hshift (by positivity) hsmall (hsja.trans hja') hW hreflect hsymbol
    hz hNz hNκ hflip (fun i ζ => R i * ja * physicalRoughField x₀ ℓ h ζ (y i)) hf
  simpa only [physicalPropensityPatternProduct, κ, z, C] using he

end CausalLowerbound.PartC
