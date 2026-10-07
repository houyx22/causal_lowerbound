import CausalLowerbound.PartC.PhysicalPolynomialDictionary
import CausalLowerbound.PartC.RepresentativeTensorSymbol

/-! Actual Q-slot density atoms retain the one-symbol volume factor.
The tensor norm and symbol bounds are uniform over the countable dictionary. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Representative

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι] {D : ℕ}

def physicalDictionaryTensor (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (m : PolynomialAtom d ι D) : Array d ι (activeBlocks (d := d) ℓ h) D :=
  tensor (fun _ : ι => physicalDictionary x₀ ℓ r h k c w N θ m)

theorem physicalDictionaryTensor_value (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ : ℝ)
    (m : PolynomialAtom d ι D) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : (ι × d) → ℝ) :
    pointValue (Wiener.torusProjection u)
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u (i, j))) ζ
      (physicalDictionaryTensor x₀ ℓ r h k c w N θ m) =
    ∏ i, (factorValue (Wiener.torusProjection (fun j => u (i, j)))
      (normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u (i, j))) ζ
      (physicalDictionary x₀ ℓ r h k c w N θ m)).re :=
  tensor_value_real _ _ _ ζ (fun _ => physicalDictionary_real x₀ ℓ r h k c w N θ m ζ _)

theorem physicalDictionaryTensor_bounds (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ y : d → ℝ, 0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (m : PolynomialAtom d ι D) :
    ‖physicalDictionaryTensor x₀ ℓ r h k c w N θ m‖ ≤ (1 + θ) ^ Fintype.card ι ∧
      (∀ ζ u, 0 < pointValue (Wiener.torusProjection u)
        (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u (i, j))) ζ
        (physicalDictionaryTensor x₀ ℓ r h k c w N θ m)) ∧
      ∀ j : activeBlocks (d := d) ℓ h,
        ‖symbolPart j (physicalDictionaryTensor x₀ ℓ r h k c w N θ m)‖ ≤
          (Fintype.card ι : ℝ) * ((θ / 2) * ((D / N₀) * (ℓ / (2 * r)) ^ Fintype.card d)) *
            (1 + θ) ^ (Fintype.card ι - 1) := by
  have hb := physicalDictionary_bounds x₀ ℓ r h k c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ hθ1 m
  refine ⟨?_, ?_, ?_⟩
  · apply (tensor_norm _).trans
    simpa using Finset.prod_le_prod (s := (Finset.univ : Finset ι))
      (fun _ _ => norm_nonneg (physicalDictionary x₀ ℓ r h k c w N θ m)) (fun _ _ => hb.1)
  · intro ζ u
    rw [physicalDictionaryTensor_value]
    exact Finset.prod_pos (fun _ _ => hb.2.1 ζ _)
  · intro j
    exact tensor_symbol_bound j (fun _ : ι => physicalDictionary x₀ ℓ r h k c w N θ m)
      (1 + θ) _ (by positivity) (by positivity)
      (fun _ => hb.1) (fun _ => hb.2.2 j)

end CausalLowerbound.PartC
