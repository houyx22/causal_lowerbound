import CausalLowerbound.PartB.NuisanceLegality
import CausalLowerbound.PartB.SignMonomials

/-! The signed quadratic-partition field used by the uniform-design experiment. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff
namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def signedField (S : Finset (d → ℤ)) (ζ : (d → ℤ) → Bool)
    (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ) : ℝ :=
  ∑ k ∈ S, sign (ζ k) * packet (coarseBump x₀ h) x₀ ℓ k x

theorem signedField_smooth (S : Finset (d → ℤ)) (ζ : (d → ℤ) → Bool)
    (x₀ : d → ℝ) (ℓ h : ℝ) : ContDiff ℝ ∞ (signedField S ζ x₀ ℓ h) := by
  apply ContDiff.sum
  intro k _
  exact contDiff_const.mul (packet_smooth _ (rescaled_smooth _ quadraticPartition_smooth _ _) _ _ _)

def signAtoms (z : Bool) : CoefficientExponent d 1 → ℝ := fun _ => sign z

theorem coefficientEvaluation_signAtoms (z : Bool) (x : d → ℝ) :
    coefficientEvaluation (signAtoms (d := d) z) x = sign z := by
  letI : Unique (CoefficientExponent d 1) :=
    { default := ⟨fun _ => 0, by simp⟩, uniq := fun _ => Subsingleton.elim _ _ }
  simp [coefficientEvaluation, signAtoms, polynomialFeature, Fin.eq_zero,
    Fintype.card_unique]

theorem signedField_eq_packetField (S : Finset (d → ℤ)) (ζ : (d → ℤ) → Bool)
    (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) :
    signedField S ζ x₀ ℓ h = packetField S (fun k => signAtoms (ζ k)) x₀ ℓ h := by
  funext x
  rw [packetField_eq_physical S _ x₀ ℓ h hℓ]
  simp only [signedField, coefficientEvaluation_signAtoms, mul_comm]

theorem signedField_amplitude_holder (s : Regularity) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (ζ : (d → ℤ) → Bool) (x₀ : d → ℝ)
      (ℓ h c : ℝ), 0 < ℓ → ℓ ≤ h → h ≤ 1 → 0 ≤ c →
      HolderControl s.order s.fraction (C * c)
        (fun x => (c * ℓ ^ s.exponent) * signedField S ζ x₀ ℓ h x) := by
  obtain ⟨C, hC, hc⟩ := propensityPerturbation_holder (signAtoms (d := d))
    s.order s.fraction s.nonneg s.le_one
  refine ⟨C, hC, ?_⟩
  intro S ζ x₀ ℓ h c hℓ hℓh hh1 hc0
  rw [signedField_eq_packetField S ζ x₀ ℓ h hℓ]
  simpa only [propensityPerturbation, Regularity.exponent, mul_comm] using
    hc S ζ x₀ ℓ h c hℓ hℓh (hℓh.trans hh1) hc0

theorem targetField_smooth (x₀ : d → ℝ) (h Δ : ℝ) :
    ContDiff ℝ ∞ (targetField x₀ h Δ) :=
  contDiff_const.mul ((rescaled_smooth _ quadraticPartition_smooth x₀ h).pow 2)

end CausalLowerbound.UniformLowerBound
