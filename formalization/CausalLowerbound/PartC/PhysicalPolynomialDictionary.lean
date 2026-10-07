import CausalLowerbound.PartC.PolynomialPolarization
import CausalLowerbound.PartC.PhysicalFactorIntegral

/-! The full countable dictionary of actual positive carrier densities,
indexed by polynomial--trigonometric tuples and two finite Boolean masks. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Representative

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι] {D : ℕ}

def physicalPolynomialCenters (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (v : PolynomialBasis d ι D) (i : ι) : Walsh.Coefficients (activeBlocks (d := d) ℓ h) :=
  normalizedTrigCenter x₀ ℓ r h k c w N (v i).1.val (v i).2.1 (v i).2.2

def physicalDictionary (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (m : PolynomialAtom d ι D) : Factor d (activeBlocks (d := d) ℓ h) D :=
  polynomialDictionary m.1 (physicalPolynomialCenters x₀ ℓ r h k c w N m.1) θ m.2

theorem physicalDictionary_real (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (m : PolynomialAtom d ι D) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    (factorValue (Wiener.torusProjection u) (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ
      (physicalDictionary x₀ ℓ r h k c w N θ m)).im = 0 :=
  polynomialDictionary_real _ _ θ m.2 _ _ ζ

theorem physicalDictionary_integral (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (hc : 0 < c) (m : PolynomialAtom d ι D) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    (∫ u in Set.Icc (0 : d → ℝ) 1, (factorValue (Wiener.torusProjection u)
      (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ (physicalDictionary x₀ ℓ r h k c w N θ m)).re) = 1 := by
  change physicalFactorIntegral x₀ ℓ r h k c w N hc ζ
    (atomFactor (fun i => physicalCenteredFactor x₀ ℓ r h k c w N
      (m.1 i).1 (m.1 i).2.1 (m.1 i).2.2) θ m.2) = 1
  exact atomFactor_linearMean _ (physicalFactorIntegral_unit _ _ _ _ _ _ _ _ hc ζ) _
    (fun i => physicalFactorIntegral_centered _ _ _ _ _ _ _ _ hc ζ _ _ _) θ m.2

theorem physicalDictionary_bounds (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ y : d → ℝ, 0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (m : PolynomialAtom d ι D) :
    ‖physicalDictionary x₀ ℓ r h k c w N θ m‖ ≤ 1 + θ ∧
      (∀ ζ u, 0 < (factorValue (Wiener.torusProjection u) (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ
        (physicalDictionary x₀ ℓ r h k c w N θ m)).re) ∧
      ∀ j : activeBlocks (d := d) ℓ h,
        ‖factorSymbol j (physicalDictionary x₀ ℓ r h k c w N θ m)‖ ≤
          (θ / 2) * ((D / N₀) * (ℓ / (2 * r)) ^ Fintype.card d) := by
  have hb (i : ι) := normalizedTrigCenter_bounds x₀ ℓ r h k c w N N₀ hℓ hr hc hN₀ hN hm hrough
    (m.1 i).1.val (m.1 i).2.1 (m.1 i).2.2
  have hcenter (i : ι) : ‖physicalCenteredFactor x₀ ℓ r h k c w N
      (m.1 i).1 (m.1 i).2.1 (m.1 i).2.2‖ ≤ 1 := centeredFactor_norm _ _ _ _ (hb i).1
  refine ⟨?_, fun ζ u => ?_, fun j => ?_⟩
  · simpa only [abs_of_nonneg hθ] using polynomialDictionary_norm m.1
      (physicalPolynomialCenters x₀ ℓ r h k c w N m.1) (fun i => (hb i).1) θ m.2
  · exact atomFactor_positive _ hcenter θ hθ hθ1 m.2 _ _
      (normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ u) ζ
  · have hcs (i : ι) : ‖factorSymbol j (physicalCenteredFactor x₀ ℓ r h k c w N
        (m.1 i).1 (m.1 i).2.1 (m.1 i).2.2)‖ ≤
          (1 / 2) * ((D / N₀) * (ℓ / (2 * r)) ^ Fintype.card d) := by
      have he : ((m.1 i).1.val : ℝ) ≤ D := by exact_mod_cast Nat.le_of_lt_succ (m.1 i).1.isLt
      exact (centeredFactor_symbol_bound j _ _ _ _).trans
        (mul_le_mul_of_nonneg_left ((hb i).2 j |>.trans
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right he hN₀.le) (by positivity))) (by norm_num))
    have hproj := atomFactor_symbol_bound
      (fun i => physicalCenteredFactor x₀ ℓ r h k c w N (m.1 i).1 (m.1 i).2.1 (m.1 i).2.2)
      θ m.2 j _ (by positivity) hcs
    simpa only [abs_of_nonneg hθ, mul_assoc, div_eq_mul_inv, one_mul] using hproj

theorem physicalDictionary_polarization [Nonempty ι] (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N θ : ℝ) (hθ : θ ≠ 0) (v : PolynomialBasis d ι D)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : (ι × d) → ℝ) :
    pointValue (Wiener.torusProjection u)
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u (i, j))) ζ
      (polynomialBasisTensor v : Array d ι (activeBlocks (d := d) ℓ h) D) =
    ∑ m : Masks ι, Walsh.evaluate ζ (Walsh.polarizationWeight
      (physicalPolynomialCenters x₀ ℓ r h k c w N v) (θ / 2) m) *
      pointValue (Wiener.torusProjection u)
        (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u (i, j))) ζ
        (tensor (fun _ : ι => physicalDictionary x₀ ℓ r h k c w N θ (v, m))) :=
  polynomial_basis_polarization v _ θ hθ _ _ ζ

end CausalLowerbound.PartC
