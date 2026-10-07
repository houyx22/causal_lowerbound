import CausalLowerbound.PartC.NaturalPhysicalDensity
import CausalLowerbound.PartC.PhysicalRepresentativeReflection
import CausalLowerbound.PartC.PairedCarrierOperator

/-! Reflection-paired physical densities, with a separate constant label.
Pairing preserves normalization, the pointwise density interval, and the
one-symbol volume gain. No quotient of representatives is used. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Representative

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι] {D : ℕ}

def pairedPhysicalDensity (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) : ℝ :=
  Sum.elim (fun m => naturalPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ m ζ u)
    (fun m => naturalPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ m (Walsh.flip ζ) u)
    (PairedSeries.labels.symm n)

def carrierPhysicalDensity (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) : ℝ :=
  match n with
  | 0 => 1
  | m + 1 => pairedPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ m ζ u

theorem pairedPhysicalDensity_continuous (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (hc : 0 < c) (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    Continuous (pairedPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ) := by
  unfold pairedPhysicalDensity
  cases PairedSeries.labels.symm n <;>
    exact naturalPhysicalDensity_continuous x₀ ℓ r h k c w N θ hc _ _

theorem pairedPhysicalDensity_integral (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (hc : 0 < c) (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    (∫ u in Set.Icc (0 : d → ℝ) 1,
      pairedPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u) = 1 := by
  unfold pairedPhysicalDensity
  cases PairedSeries.labels.symm n <;>
    exact naturalPhysicalDensity_integral x₀ ℓ r h k c w N θ hc _ _

theorem pairedPhysicalAtom_value (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : (ι × d) → ℝ) :
    pointValue (Wiener.torusProjection u)
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u (i, j))) ζ
      (pairedAtom reflection (naturalPhysicalAtom (D := D) x₀ ℓ r h k c w N θ) n) =
        ∏ i, pairedPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ (fun j => u (i, j)) := by
  unfold pairedAtom pairedPhysicalDensity
  cases PairedSeries.labels.symm n with
  | inl m => exact naturalPhysicalAtom_value x₀ ℓ r h k c w N θ m ζ u
  | inr m =>
    rw [Sum.elim_inr, physical_pointValue_reflection]
    exact naturalPhysicalAtom_value x₀ ℓ r h k c w N θ m (Walsh.flip ζ) u

theorem pairedPhysicalDensity_range (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ y : d → ℝ, 0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 ≤ θ)
    (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    1 - θ ≤ pairedPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u ∧
      pairedPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u ≤ 1 + θ := by
  unfold pairedPhysicalDensity
  cases PairedSeries.labels.symm n <;>
    exact naturalPhysicalDensity_range x₀ ℓ r h k c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ _ _ u

theorem pairedPhysicalAtom_symbol_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ y : d → ℝ, 0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (n : ℕ) (j : activeBlocks (d := d) ℓ h) :
    ‖symbolPart j (pairedAtom reflection
      (naturalPhysicalAtom (ι := ι) (D := D) x₀ ℓ r h k c w N θ) n)‖ ≤
      (Fintype.card ι : ℝ) * ((θ / 2) * ((D / N₀) * (ℓ / (2 * r)) ^ Fintype.card d)) *
        (1 + θ) ^ (Fintype.card ι - 1) := by
  unfold pairedAtom
  cases PairedSeries.labels.symm n with
  | inl m =>
    exact naturalPhysicalAtom_symbol_bound x₀ ℓ r h k c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ hθ1 m j
  | inr m =>
    rw [Sum.elim_inr, symbolPart_reflection, reflection_norm]
    exact naturalPhysicalAtom_symbol_bound x₀ ℓ r h k c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ hθ1 m j

theorem carrierPhysicalDensity_continuous (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (hc : 0 < c) (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    Continuous (carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ) := by
  cases n with
  | zero => exact continuous_const
  | succ m => exact pairedPhysicalDensity_continuous x₀ ℓ r h k c w N θ hc m ζ

theorem carrierPhysicalDensity_integral (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (hc : 0 < c) (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    (∫ u in Set.Icc (0 : d → ℝ) 1,
      carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u) = 1 := by
  cases n with
  | zero => simp [carrierPhysicalDensity, setIntegral_const, measureReal_def, Real.volume_Icc_pi]
  | succ m => exact pairedPhysicalDensity_integral x₀ ℓ r h k c w N θ hc m ζ

theorem carrierPhysicalDensity_range (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ y : d → ℝ, 0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 ≤ θ)
    (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    1 - θ ≤ carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u ∧
      carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u ≤ 1 + θ := by
  cases n with
  | zero => change 1 - θ ≤ 1 ∧ 1 ≤ 1 + θ; constructor <;> linarith
  | succ m => exact pairedPhysicalDensity_range x₀ ℓ r h k c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ m ζ u

theorem carrierPhysicalAtom_value (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : (ι × d) → ℝ) :
    pointValue (Wiener.torusProjection u)
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u (i, j))) ζ
      (CarrierCoefficients.labeledAtom unit
        (pairedAtom reflection (naturalPhysicalAtom (D := D) x₀ ℓ r h k c w N θ)) n) =
        ∏ i, carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ (fun j => u (i, j)) := by
  cases n with
  | zero => simp only [CarrierCoefficients.labeledAtom, carrierPhysicalDensity, pointValue_unit, Finset.prod_const_one]
  | succ m => exact pairedPhysicalAtom_value x₀ ℓ r h k c w N θ m ζ u

end CausalLowerbound.PartC
