import CausalLowerbound.PartC.SignCarrierMoments

/-! The common-label fixed point with sign-dependent coefficient kernels.
The analytic input is a norm-controlled coefficient map and its actual
reconstruction after evaluation. Positive density atoms and the concrete
polarization still have to be supplied by the mixed-case construction. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB

variable {E V F Z I Γ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype Γ]

/-- The label law and representative fixed point are chosen once for all sign
vectors. Both the density and weighted moment identities are convergent series,
and every coefficient kernel is a genuine strictly positive finite law. -/
theorem exists_sign_carrier {L : ℝ} (A : CarrierCoefficients E V L)
    (ev : Z → I → V →ₗ[ℝ] ℝ) (hev : ∀ ζ i a, |ev ζ i a| ≤ ‖a‖)
    (evalDensity : Z → E →L[ℝ] F)
    (e : E) (he : ‖e‖ ≤ 1) (atom : ℕ → E) (M : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hatom : ∀ m, ‖atom m - e‖ ≤ M)
    (target : E → Z → I → F)
    (hreconstruct : ∀ D ζ i, HasSum
      (fun m => ev ζ i (A.coeff D m) • evalDensity ζ (atom m)) (target D ζ i))
    (feature : I → Γ → ℝ) (μ : FiniteLaw Γ) (hμ : ∀ x, 0 < μ.weight x)
    (radius : ℝ)
    (realize : ∀ v : I → ℝ, (∀ i, |v i| ≤ radius) →
      ∃ ν : FiniteLaw Γ, (∀ x, 0 < ν.weight x) ∧
        ∀ i, ν.expect (feature i) = μ.expect (feature i) + v i)
    (K : ℝ) (hK : 0 < K) (hinv : K⁻¹ ≤ radius)
    (hsmall : K * M * L ≤ 1 / 2) (hmass : 2 * K * L < 1) :
    ∃ (D : E) (H : DiscreteLaw ℕ) (kernel : Z → ℕ → FiniteLaw Γ),
      A.update K e atom D = D ∧
      ‖D - e‖ ≤ 2 * (K * M * L) ∧
      0 < H.weight 0 ∧
      (∀ m, H.weight (m + 1) = K * ‖A.coeff D m‖) ∧
      (∀ ζ, kernel ζ 0 = μ) ∧
      (∀ ζ n x, 0 < (kernel ζ n).weight x) ∧
      (∀ ζ n, (∑ x, (H.joint (kernel ζ)).weight (n, x)) = H.weight n) ∧
      HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom e atom n) D ∧
      (∀ ζ, HasSum (fun n => H.weight n •
        evalDensity ζ (CarrierCoefficients.labeledAtom e atom n)) (evalDensity ζ D)) ∧
      ∀ ζ i, HasSum (fun n => (H.weight n *
        ((kernel ζ n).expect (feature i) - μ.expect (feature i))) •
        CarrierCoefficients.labeledAtom (evalDensity ζ e)
          (fun m => evalDensity ζ (atom m)) n) (target D ζ i) := by
  obtain ⟨D, hfixed, hball, htotal, _⟩ :=
    A.exists_unique_positive_fixed_point K M hK.le hM hL e he atom hatom hsmall hmass
  let H := A.labelLaw K hK.le D htotal.le
  have hweight : ∀ m, H.weight (m + 1) = K * ‖A.coeff D m‖ := fun _ => rfl
  have hdensity := A.fixed_point_density_hasSum K hK.le D e atom M hatom htotal.le hfixed
  obtain ⟨kernel, hzero, hpos, hmom⟩ :=
    exists_sign_carrier_kernel feature μ radius realize ev hev (A.coeff D) K hK hinv
  refine ⟨D, H, kernel, hfixed, hball, ?_, hweight, hzero, ?_, ?_, hdensity, ?_, ?_⟩
  · change 0 < 1 - A.mass K D
    exact sub_pos.mpr htotal
  · intro ζ n x
    cases n with
    | zero => simpa only [hzero ζ] using hμ x
    | succ m => exact hpos ζ m x
  · intro ζ n
    exact H.joint_label_marginal (kernel ζ) n
  · intro ζ
    simpa only [map_smul] using (evalDensity ζ).hasSum hdensity
  · intro ζ i
    exact sign_carrier_moment_hasSum feature μ (ev ζ) (A.coeff D) K hK H hweight
      (kernel ζ) (hzero ζ) (hmom ζ) (evalDensity ζ e)
      (fun m => evalDensity ζ (atom m)) (target D ζ) (hreconstruct D ζ) i

end CausalLowerbound.PartC
