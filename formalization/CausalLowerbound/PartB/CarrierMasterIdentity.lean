import CausalLowerbound.PartB.CarrierProjectivity
import CausalLowerbound.PartB.PaperWiener

/-! The Banach-space carrier identity evaluated at actual sites. This is
the bridge from the Wiener fixed point to the probability-weighted moments. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d Γ I : Type*} [Fintype d] [DecidableEq d] [Fintype Γ] [Fintype I]

def carrierEvaluation (Q : ℕ) (u : Fin Q → Torus d) : SymmetricReal d (Fin Q) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((evaluation (fun ij => u ij.1 ij.2)).comp symmetricInclusion)

theorem carrierEvaluation_mul (Q : ℕ) (u : Fin Q → Torus d)
    (a b : SymmetricReal d (Fin Q)) :
    carrierEvaluation Q u (a * b) = carrierEvaluation Q u a * carrierEvaluation Q u b := by
  change (toContinuous ((a : Fourier (Fin Q × d)) * (b : Fourier (Fin Q × d))) _).re = _
  simp only [toContinuous_mul, ContinuousMap.mul_apply, Complex.mul_re, a.property.1, zero_mul, sub_zero]
  rfl

theorem carrierEvaluation_atom (Q : ℕ) (θ : ℝ) (label : ℕ) (u : Fin Q → Torus d) :
    carrierEvaluation Q u
      (CarrierCoefficients.labeledAtom 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) θ) label) =
      densityTensor Q θ label u := by
  cases label with
  | zero => simp [carrierEvaluation, CarrierCoefficients.labeledAtom, densityTensor, labeledDensity,
      ContinuousLinearMap.comp_apply]
  | succ n =>
    change (toContinuous (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) θ n : Fourier (Fin Q × d)) _).re = _
    rw [PositiveWiener.naturalAtom_factorization, tensor_value]
    have he (i : Fin Q) : toContinuous (PositiveWiener.naturalDensity (ι := Fin Q) θ n) (u i) =
        (labeledDensity Q θ (n + 1) (u i) : ℂ) := by
      apply Complex.ext
      · rfl
      · exact PositiveWiener.naturalDensity_real θ n (u i)
    simp only [he, ← Complex.ofReal_prod, Complex.ofReal_re, densityTensor]

theorem carrier_density_value (Q : ℕ) (θ : ℝ) (H : DiscreteLaw ℕ)
    (D : SymmetricReal d (Fin Q))
    (hD : HasSum (fun label => H.weight label •
      CarrierCoefficients.labeledAtom 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) θ) label) D)
    (u : Fin Q → Torus d) : carrierEvaluation Q u D = densityMoment H Q θ u := by
  have he := (carrierEvaluation Q u).hasSum hD
  simp only [map_smul, smul_eq_mul, carrierEvaluation_atom] at he
  exact he.tsum_eq.symm

theorem carrier_master_pointwise (Q : ℕ) (θ : ℝ) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw Γ) (μ : FiniteLaw Γ) (feature : I → Γ → ℝ)
    (D : SymmetricReal d (Fin Q)) (J : I → SymmetricReal d (Fin Q))
    (hD : HasSum (fun label => H.weight label •
      CarrierCoefficients.labeledAtom 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) θ) label) D)
    (hJ : ∀ i, HasSum (fun label => (H.weight label *
        ((kernel label).expect (feature i) - μ.expect (feature i))) •
      CarrierCoefficients.labeledAtom 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) θ) label) (D * J i))
    (u : Fin Q → Torus d) (i : I) :
    H.expect (fun label => densityTensor Q θ label u *
      ((kernel label).expect (feature i) - μ.expect (feature i))) =
      densityMoment H Q θ u * carrierEvaluation Q u (J i) := by
  have he := (carrierEvaluation Q u).hasSum (hJ i)
  simp only [map_smul, smul_eq_mul, carrierEvaluation_atom, carrierEvaluation_mul,
    carrier_density_value Q θ H D hD u] at he
  rw [← he.tsum_eq]
  apply tsum_congr
  intro label
  ring

/-- No additional scalar master-moment assumption is introduced: it follows
from the previously constructed positive carrier. -/
theorem hasPositiveCarrier_pointwise (Q : ℕ) (θ : ℝ)
    (J : I → SymmetricReal d (Fin Q)) (feature : I → Γ → ℝ) (μ : FiniteLaw Γ)
    (hc : HasPositiveCarrier 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) θ)
      (multiplicationIncrement J) feature μ) :
    ∃ (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Γ),
      0 < H.weight 0 ∧ (∀ label x, 0 < (kernel label).weight x) ∧
      ∀ u i, H.expect (fun label => densityTensor Q θ label u *
        ((kernel label).expect (feature i) - μ.expect (feature i))) =
          densityMoment H Q θ u * carrierEvaluation Q u (J i) := by
  obtain ⟨D, H, kernel, h0, hk, _, hD, hJ⟩ := hc
  exact ⟨H, kernel, h0, hk, carrier_master_pointwise Q θ H kernel μ feature D J hD hJ⟩

end CausalLowerbound.PartB.ShellGeometry

