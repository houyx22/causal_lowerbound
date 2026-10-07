import CausalLowerbound.PartC.PairedCarrierOperator
import CausalLowerbound.PartC.SignCarrierConstruction

/-! A positive common-label carrier with separately retained reflected
density tensors. The fixed point and label law are invariant under the
pairing, while its weighted moment difference is the given target. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB

variable {E V F Z I Γ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype Γ]

theorem exists_paired_sign_carrier
    (A B : E →L[ℝ] VectorSeries.Family ℕ V) (L₁ L₂ : ℝ)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hA : ∀ D, ‖A D‖ ≤ L₁ * ‖D‖) (hB : ∀ D, ‖B D‖ ≤ L₂ * ‖D‖)
    (R : E →L[ℝ] E) (hRinv : ∀ D, R (R D) = D) (hRnorm : ∀ D, ‖R D‖ ≤ ‖D‖)
    (e : E) (he : ‖e‖ ≤ 1) (hRe : R e = e) (atom : ℕ → E)
    (M : ℝ) (hM : 0 ≤ M) (hatom : ∀ n, ‖atom n - e‖ ≤ M)
    (ev : Z → I → V →ₗ[ℝ] ℝ) (hev : ∀ ζ i a, |ev ζ i a| ≤ ‖a‖)
    (evalDensity : Z → E →L[ℝ] F) (target : E → Z → I → F)
    (hplus : ∀ D ζ i, HasSum (fun n => ev ζ i (A D n) • evalDensity ζ (atom n)) (target D ζ i))
    (hminus : ∀ D ζ i, HasSum (fun n => ev ζ i (B D n) • evalDensity ζ (R (atom n))) (target D ζ i))
    (feature : I → Γ → ℝ) (μ : FiniteLaw Γ) (hμ : ∀ x, 0 < μ.weight x) (radius : ℝ)
    (realize : ∀ v : I → ℝ, (∀ i, |v i| ≤ radius) →
      ∃ ν : FiniteLaw Γ, (∀ x, 0 < ν.weight x) ∧
        ∀ i, ν.expect (feature i) = μ.expect (feature i) + v i)
    (K : ℝ) (hK : 0 < K) (hinv : K⁻¹ ≤ radius)
    (hsmall : K * M * (L₁ + L₂) ≤ 1 / 2) (hmass : 2 * K * (L₁ + L₂) < 1) :
    let C := pairedCarrierCoefficients A B L₁ L₂ hA hB
    ∃ (D : E) (H : DiscreteLaw ℕ) (kernel : Z → ℕ → FiniteLaw Γ),
      C.update K e (pairedAtom R atom) D = D ∧ R D = D ∧
      ‖D - e‖ ≤ 2 * (K * M * (L₁ + L₂)) ∧ 0 < H.weight 0 ∧
      (∀ n, H.weight (n + 1) = K * ‖C.coeff D n‖) ∧
      (∀ n, H.weight (PairedSeries.flipLabel n + 1) = H.weight (n + 1)) ∧
      (∀ ζ, kernel ζ 0 = μ) ∧ (∀ ζ n x, 0 < (kernel ζ n).weight x) ∧
      (∀ ζ n, (∑ x, (H.joint (kernel ζ)).weight (n, x)) = H.weight n) ∧
      HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom e (pairedAtom R atom) n) D ∧
      (∀ ζ, HasSum (fun n => H.weight n •
        evalDensity ζ (CarrierCoefficients.labeledAtom e (pairedAtom R atom) n)) (evalDensity ζ D)) ∧
      ∀ ζ i, HasSum (fun n => (H.weight n *
        ((kernel ζ n).expect (feature i) - μ.expect (feature i))) •
        CarrierCoefficients.labeledAtom (evalDensity ζ e)
          (fun m => evalDensity ζ (pairedAtom R atom m)) n) (target D ζ i) := by
  let C := pairedCarrierCoefficients A B L₁ L₂ hA hB
  have hpaired : ∀ n, ‖pairedAtom R atom n - e‖ ≤ M := pairedAtom_bound R hRnorm e hRe atom M hatom
  have hreconstruct (D : E) (ζ : Z) (i : I) :
      HasSum (fun n => firstEvaluation (ev ζ i) (C.coeff D n) •
        evalDensity ζ (pairedAtom R atom n)) (target D ζ i) := by
    have hs := pairedCoefficient_reconstruction (A D) (B D) (ev ζ i)
      (fun n => evalDensity ζ (atom n)) (fun n => evalDensity ζ (R (atom n)))
      (target D ζ i) (hplus D ζ i) (hminus D ζ i)
    apply hs.congr_fun
    intro n
    congr 1
    unfold pairedAtom
    cases PairedSeries.labels.symm n <;> rfl
  obtain ⟨D, H, kernel, hfixed, hball, hzeroMass, hweight, hzero, hpositive, hmarginal, hdensity, heval, hmoment⟩ :=
    exists_sign_carrier C (fun ζ i => firstEvaluation (ev ζ i))
      (fun ζ i => firstEvaluation_bound (ev ζ i) (hev ζ i)) evalDensity e he (pairedAtom R atom)
      M hM (add_nonneg hL₁ hL₂) hpaired target hreconstruct
      feature μ hμ radius realize K hK hinv hsmall hmass
  refine ⟨D, H, kernel, hfixed, ?_, hball, hzeroMass, hweight, ?_,
    hzero, hpositive, hmarginal, hdensity, heval, hmoment⟩
  · exact carrier_fixed_point_invariant C K hK.le e (pairedAtom R atom) M hpaired R hRe
      PairedSeries.flipLabel (pairedAtom_reflection R hRinv atom)
      (pairedCarrierCoefficients_equal_weights A B L₁ L₂ hA hB) D hfixed
  · intro n
    rw [hweight, hweight, pairedCarrierCoefficients_equal_weights A B L₁ L₂ hA hB]

end CausalLowerbound.PartC
