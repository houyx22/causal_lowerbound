import CausalLowerbound.PartC.NaturalPolynomialPolarization
import CausalLowerbound.PartC.PhysicalPolynomialTensor

/-! The actual one-point densities behind the natural-number atom list.
Every label, including unused encodings, has integral one. Their products
are exactly the evaluated representative atoms. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Representative

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι] {D : ℕ}

local instance polynomialAtomEncodable : Encodable (PolynomialAtom d ι D) := Encodable.ofCountable _

def naturalPhysicalDensity (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) : ℝ :=
  match Encodable.decode (α := PolynomialAtom d ι D) n with
  | some m => (factorValue (Wiener.torusProjection u)
      (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ (physicalDictionary x₀ ℓ r h k c w N θ m)).re
  | none => 1

def naturalPhysicalAtom (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (n : ℕ) : Array d ι (activeBlocks (d := d) ℓ h) D :=
  naturalPolynomialAtom (physicalPolynomialCenters x₀ ℓ r h k c w N) θ n

theorem naturalPhysicalDensity_continuous (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (hc : 0 < c) (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    Continuous (naturalPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ) := by
  unfold naturalPhysicalDensity
  cases Encodable.decode (α := PolynomialAtom d ι D) n with
  | none => exact continuous_const
  | some m =>
    exact Complex.continuous_re.comp (factorValue_continuous _ Wiener.torusProjection_quotient.continuous _
      (normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ) ζ _)

theorem naturalPhysicalDensity_integral (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (hc : 0 < c) (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    (∫ u in Set.Icc (0 : d → ℝ) 1,
      naturalPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u) = 1 := by
  unfold naturalPhysicalDensity
  cases Encodable.decode (α := PolynomialAtom d ι D) n with
  | none => simp [setIntegral_const, measureReal_def, Real.volume_Icc_pi]
  | some m => exact physicalDictionary_integral x₀ ℓ r h k c w N θ hc m ζ

theorem naturalPhysicalAtom_value (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : (ι × d) → ℝ) :
    pointValue (Wiener.torusProjection u)
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u (i, j))) ζ
      (naturalPhysicalAtom (D := D) x₀ ℓ r h k c w N θ n) =
        ∏ i, naturalPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ (fun j => u (i, j)) := by
  unfold naturalPhysicalAtom naturalPolynomialAtom naturalPhysicalDensity
  cases Encodable.decode (α := PolynomialAtom d ι D) n with
  | none => simp only [pointValue_unit, Finset.prod_const_one]
  | some m => exact physicalDictionaryTensor_value x₀ ℓ r h k c w N θ m ζ u

theorem naturalPhysicalDensity_range (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ y : d → ℝ, 0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 ≤ θ)
    (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    1 - θ ≤ naturalPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u ∧
      naturalPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u ≤ 1 + θ := by
  unfold naturalPhysicalDensity
  cases Encodable.decode (α := PolynomialAtom d ι D) n with
  | none => change 1 - θ ≤ 1 ∧ 1 ≤ 1 + θ; constructor <;> linarith
  | some m =>
    have hcenter (i : ι) : ‖physicalCenteredFactor x₀ ℓ r h k c w N
        (m.1 i).1 (m.1 i).2.1 (m.1 i).2.2‖ ≤ 1 :=
      centeredFactor_norm _ _ _ _ (normalizedTrigCenter_bounds x₀ ℓ r h k c w N N₀
        hℓ hr hc hN₀ hN hm hrough (m.1 i).1.val (m.1 i).2.1 (m.1 i).2.2).1
    exact atomFactor_range _ hcenter θ hθ m.2 _ _
      (normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ u) ζ

theorem naturalPhysicalAtom_symbol_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ y : d → ℝ, 0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (n : ℕ) (j : activeBlocks (d := d) ℓ h) :
    ‖symbolPart j (naturalPhysicalAtom (ι := ι) (D := D) x₀ ℓ r h k c w N θ n)‖ ≤
      (Fintype.card ι : ℝ) * ((θ / 2) * ((D / N₀) * (ℓ / (2 * r)) ^ Fintype.card d)) *
        (1 + θ) ^ (Fintype.card ι - 1) := by
  unfold naturalPhysicalAtom naturalPolynomialAtom
  cases Encodable.decode (α := PolynomialAtom d ι D) n with
  | none => rw [symbolPart_unit, norm_zero]; positivity
  | some m =>
    exact (physicalDictionaryTensor_bounds x₀ ℓ r h k c w N N₀ θ
      hℓ hr hc hN₀ hN hm hrough hθ hθ1 m).2.2 j

end CausalLowerbound.PartC
