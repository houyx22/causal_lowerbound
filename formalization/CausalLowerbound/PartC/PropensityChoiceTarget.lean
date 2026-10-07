import CausalLowerbound.PartC.PropensitySubstitution
import CausalLowerbound.PartC.ShiftChoiceWiener

/-! The multilinear part of the actual virtual-shift expansion defines
the degree-one target. A choice is retained exactly when no site occurs
twice. The construction acts on representative arrays before evaluation. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative

variable {Ω K V E d J : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype d] [DecidableEq d]
  [Fintype J] [DecidableEq J]

def propensityChoiceTarget (k : V → Fourier (V × d)) (hk : ∀ i, ‖k i‖ ≤ 1)
    (A : (K → Option V) → Fourier (V × d)) :
    Representative.Array d V J 1 →L[ℝ] Representative.Array d V J 1 :=
  ∑ s : K → Option V, if Function.Injective (choiceSite s) then
    propensityPattern (choiceSites s) k hk (A s) else 0

theorem propensityChoiceTarget_bound (k : V → Fourier (V × d)) (hk : ∀ i, ‖k i‖ ≤ 1)
    (A : (K → Option V) → Fourier (V × d)) (v : Representative.Array d V J 1) :
    ‖propensityChoiceTarget k hk A v‖ ≤ (∑ s, ‖A s‖) * ‖v‖ := by
  simp only [propensityChoiceTarget, ContinuousLinearMap.sum_apply]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s _
  split_ifs
  · exact propensityPattern_bound (choiceSites s) k hk (A s) v
  · simpa only [ContinuousLinearMap.zero_apply, norm_zero] using mul_nonneg (norm_nonneg (A s)) (norm_nonneg v)

theorem propensityChoiceTarget_symbol (k : V → Fourier (V × d)) (hk : ∀ i, ‖k i‖ ≤ 1)
    (A : (K → Option V) → Fourier (V × d)) (v : Representative.Array d V J 1) (j : J) :
    symbolPart j (propensityChoiceTarget k hk A v) = propensityChoiceTarget k hk A (symbolPart j v) := by
  simp only [propensityChoiceTarget, ContinuousLinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · exact degreeSubstitution_symbolProject _ _ _ _ (fun S => j ∈ S) v
  · simp

theorem propensityChoiceTarget_symbol_bound (k : V → Fourier (V × d)) (hk : ∀ i, ‖k i‖ ≤ 1)
    (A : (K → Option V) → Fourier (V × d)) (v : Representative.Array d V J 1) (j : J) :
    ‖symbolPart j (propensityChoiceTarget k hk A v)‖ ≤ (∑ s, ‖A s‖) * ‖symbolPart j v‖ := by
  rw [propensityChoiceTarget_symbol]
  exact propensityChoiceTarget_bound k hk A _

theorem propensityChoiceTarget_remove (k : V → Fourier (V × d)) (hk : ∀ i, ‖k i‖ ≤ 1)
    (A : (K → Option V) → Fourier (V × d)) (v : Representative.Array d V J 1) (S : Finset J) :
    remove S (propensityChoiceTarget k hk A v) = propensityChoiceTarget k hk A (remove S v) := by
  simp only [propensityChoiceTarget, ContinuousLinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · exact propensityPattern_remove (choiceSites s) k hk (A s) v S
  · simp

theorem propensityChoiceTarget_value (k : V → Fourier (V × d)) (hk : ∀ i, ‖k i‖ ≤ 1)
    (A : (K → Option V) → Fourier (V × d)) (v : Representative.Array d V J 1)
    (x : Torus (V × d)) (z : V → ℝ) (ζ : J → Bool)
    (hA : ∀ s, (toContinuous (A s) x).im = 0) (hkre : ∀ i, (toContinuous (k i) x).im = 0) :
    pointValue x z ζ (propensityChoiceTarget k hk A v) =
      ∑ s : K → Option V, if Function.Injective (choiceSite s) then
        (toContinuous (A s) x).re * ∑ r : Row V J 1,
          Walsh.character r.2 ζ * (toContinuous (v r) x).re *
            ∏ i, propensitySlotFactor (choiceSites s) (fun j => (toContinuous (k j) x).re) z r.1 i
        else 0 := by
  simp only [propensityChoiceTarget, ContinuousLinearMap.sum_apply, pointValue_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · exact propensityPattern_value (choiceSites s) k hk (A s) v x z ζ (hA s) hkre
  · exact pointValue_zero x z ζ

/-- This value is the prescribed design-weighted, multilinear shift,
written before averaging any rough signs. -/
def propensityChoiceValue (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (amp t : ℝ) (κ : V → ℝ) (v : Representative.Array d V J 1)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) : ℝ :=
  ∑ s : K → Option V, if Function.Injective (choiceSite s) then
    shiftChoiceCoefficient a b μ U ν amp t s u * ∑ r : Row V J 1,
      Walsh.character r.2 ζ * (toContinuous (v r) (torusProjection u)).re *
        ∏ i, propensitySlotFactor (choiceSites s) κ z r.1 i
    else 0

theorem exists_propensityChoiceTarget (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) :
    ∃ C ≥ 0, ∀ (J : Type*) [Fintype J] [DecidableEq J],
      ∀ amp ≥ 0, ∀ t > 0, ∀ (k : V → Fourier (V × d)) (hk : ∀ i, ‖k i‖ ≤ 1),
      ∃ T : Representative.Array d V J 1 →L[ℝ] Representative.Array d V J 1,
        (∀ v, ‖T v‖ ≤ (C * ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E *
          ∑ j ∈ Finset.Icc 1 (Fintype.card K), (amp / t) ^ j) * ‖v‖) ∧
        (∀ v S, remove S (T v) = T (remove S v)) ∧
        ∀ v u z ζ, (∀ i, (toContinuous (k i) (torusProjection u)).im = 0) →
          pointValue (torusProjection u) z ζ (T v) =
            propensityChoiceValue a b μ U ν amp t
              (fun i => (toContinuous (k i) (torusProjection u)).re) v u z ζ := by
  obtain ⟨C, hC, hcoeff⟩ := exists_shiftChoiceWiener a b μ U ν
  refine ⟨C, hC, fun J _ _ amp hamp t ht k hk => ?_⟩
  obtain ⟨A, hA, hn⟩ := hcoeff amp hamp t ht
  refine ⟨propensityChoiceTarget k hk A, fun v => (propensityChoiceTarget_bound k hk A v).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg v)), propensityChoiceTarget_remove k hk A, ?_⟩
  intro v u z ζ hkre
  rw [propensityChoiceTarget_value k hk A v _ z ζ (fun s => by rw [hA]; rfl) hkre]
  simp only [propensityChoiceValue, hA, Complex.ofReal_re]

end CausalLowerbound.PartC
