import CausalLowerbound.PartB.CarrierMoments

/-!
# Conditional construction of the positive pre-data carrier

The input is an actual summable linear polarization with a reconstruction
identity, a small linear ideal increment, and a finite moment radius. All
probability and fixed-point conclusions are then constructed. These inputs
are the remaining Wiener/polynomial obligations, not new mathematical axioms.
-/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : Type*} [Fintype I]

/-- The outputs of `B:lem:positive-polarization` needed by the fixed-point proof.
Pointwise positivity and unit integral of the density atoms are separate facts
about the concrete Wiener realization; they are not established by this interface. -/
structure CarrierPolarization (E I : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype I] (e : E) (C M : ℝ) where
  atom : ℕ → E
  atom_bound : ∀ m, ‖atom m - e‖ ≤ M
  coefficients : (I → E) →ₗ[ℝ] (ℕ → I → ℝ)
  summable_norm : ∀ T, Summable (fun m => ‖coefficients T m‖)
  norm_bound : ∀ T, (∑' m, ‖coefficients T m‖) ≤ C * ‖T‖
  reconstruction : ∀ T i, HasSum (fun m => coefficients T m i • atom m) (T i)

namespace CarrierPolarization

variable {e : E} {C M : ℝ} (P : CarrierPolarization E I e C M)

/-- Compose polarization with multiplication by the ideal moment increment.
The caller supplies the linear multiplication map and its norm estimate. -/
def composeIncrement (J : E →ₗ[ℝ] (I → E)) (δ : ℝ) (hC : 0 ≤ C)
    (hJ : ∀ D, ‖J D‖ ≤ δ * ‖D‖) : CarrierCoefficients E (I → ℝ) (C * δ) where
  coeff D := P.coefficients (J D)
  summable_norm D := P.summable_norm (J D)
  zero m := by simp only [map_zero, Pi.zero_apply]
  difference_bound D D' := by
    have h := P.norm_bound (J (D - D'))
    simp only [map_sub, Pi.sub_apply] at h
    calc
      _ ≤ C * ‖J D - J D'‖ := h
      _ = C * ‖J (D - D')‖ := by rw [map_sub]
      _ ≤ C * (δ * ‖D - D'‖) := mul_le_mul_of_nonneg_left (hJ (D - D')) hC
      _ = _ := by ring

variable [CompleteSpace E] {Γ : Type*} [Fintype Γ]

/-- All finite moment and Banach-space inputs are connected here. One common
label law both generates D and carries the exact moment increment J(D).

This is conditional on a concrete polarization and a concrete moment radius;
it does not claim to construct the paper's Wiener atoms or interpolation points. -/
theorem exists_positive_carrier (J : E →ₗ[ℝ] (I → E)) (δ : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (he : ‖e‖ ≤ 1)
    (hJ : ∀ D, ‖J D‖ ≤ δ * ‖D‖)
    (feature : I → Γ → ℝ) (μ : FiniteLaw Γ) (hμ : ∀ x, 0 < μ.weight x)
    (radius : ℝ)
    (realize : ∀ v : I → ℝ, (∀ i, |v i| ≤ radius) →
      ∃ ν : FiniteLaw Γ, (∀ x, 0 < ν.weight x) ∧
        ∀ i, ν.expect (feature i) = μ.expect (feature i) + v i)
    (K : ℝ) (hK : 0 < K) (hinv : K⁻¹ ≤ radius)
    (hsmall : K * M * (C * δ) ≤ 1 / 2) (hmass : 2 * K * (C * δ) < 1) :
    ∃ (D : E) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Γ),
      ‖D - e‖ ≤ 2 * (K * M * (C * δ)) ∧
      0 < H.weight 0 ∧
      (∀ n x, 0 < (kernel n).weight x) ∧
      (∀ n, (∑ x, (H.joint kernel).weight (n, x)) =
        ∑ x, (H.joint (fun _ => μ)).weight (n, x)) ∧
      HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom e P.atom n) D ∧
      ∀ i, HasSum (fun n => (H.weight n *
          ((kernel n).expect (feature i) - μ.expect (feature i))) •
        CarrierCoefficients.labeledAtom e P.atom n) (J D i) := by
  let A := P.composeIncrement J δ hC hJ
  obtain ⟨D, hfixed, hball, htotal, _⟩ :=
    A.exists_unique_positive_fixed_point K M hK.le hM (mul_nonneg hC hδ)
      e he P.atom P.atom_bound hsmall hmass
  let H := A.labelLaw K hK.le D htotal.le
  obtain ⟨kernel, hzero, hpos, hmom⟩ := exists_carrier_kernel feature μ radius realize
    (A.coeff D) K hK hinv
  refine ⟨D, H, kernel, hball, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 < 1 - A.mass K D
    exact sub_pos.mpr htotal
  · intro n x
    cases n with
    | zero => simpa only [hzero] using hμ x
    | succ m => exact hpos m x
  · intro n
    rw [DiscreteLaw.joint_label_marginal, DiscreteLaw.joint_label_marginal]
  · exact A.fixed_point_density_hasSum K hK.le D e P.atom M P.atom_bound htotal.le hfixed
  · intro i
    let s : ℕ → E := fun n => (H.weight n *
      ((kernel n).expect (feature i) - μ.expect (feature i))) •
      CarrierCoefficients.labeledAtom e P.atom n
    have hz : s 0 = 0 := by simp [s, hzero]
    have htail : ∀ m, s (m + 1) = A.coeff D m i • P.atom m := by
      intro m
      have heq := congrFun (normalizedCoefficient_scale K hK (A.coeff D m)) i
      change (K * ‖A.coeff D m‖) * normalizedCoefficient K (A.coeff D m) i =
        A.coeff D m i at heq
      change (A.weight K D m * ((kernel (m + 1)).expect (feature i) -
        μ.expect (feature i))) • P.atom m = _
      rw [hmom m i]
      simp only [add_sub_cancel_left, CarrierCoefficients.weight, heq]
    have hs : HasSum (fun m => s (m + 1)) (J D i) := by
      simpa only [htail] using P.reconstruction (J D) i
    have h := (hasSum_nat_add_iff (f := s) 1).mp hs
    simpa only [Finset.sum_range_one, hz, add_zero] using h

end CarrierPolarization

section Multiplication

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- The actual linear map D ↦ D*J used for the ideal moment increment. -/
def multiplicationIncrement (J : I → B) : B →ₗ[ℝ] (I → B) where
  toFun D i := D * J i
  map_add' D D' := by funext i; exact add_mul D D' (J i)
  map_smul' r D := by funext i; exact smul_mul_assoc r D (J i)

theorem multiplicationIncrement_bound (J : I → B) (δ : ℝ)
    (hδ : 0 ≤ δ) (hJ : ‖J‖ ≤ δ) (D : B) :
    ‖multiplicationIncrement J D‖ ≤ δ * ‖D‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hδ (norm_nonneg D))).mpr
  intro i
  calc
    _ ≤ ‖D‖ * ‖J i‖ := norm_mul_le D (J i)
    _ ≤ ‖D‖ * ‖J‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm J i) (norm_nonneg D)
    _ ≤ ‖D‖ * δ := mul_le_mul_of_nonneg_left hJ (norm_nonneg D)
    _ = _ := mul_comm _ _

end Multiplication

open Filter
open scoped Topology

/-- The analytic statement δ_n → 0 supplies both smallness thresholds. -/
theorem eventually_carrier_smallness (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (K M C : ℝ) :
    ∀ᶠ n in atTop, K * M * (C * δ n) ≤ 1 / 2 ∧ 2 * K * (C * δ n) < 1 := by
  have hq : Tendsto (fun n => K * M * (C * δ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_const_nhds.mul hδ)
  have hw : Tendsto (fun n => 2 * K * (C * δ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_const_nhds.mul hδ)
  filter_upwards [hq.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    hw.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hq hw
  exact ⟨hq.le, hw⟩

/-- A common-label carrier with a positive residual label and exact density
and moment identities. Concrete density-atom legality is supplied separately. -/
def HasPositiveCarrier {Γ : Type*} [Fintype Γ] (e : E) (atom : ℕ → E)
    (J : E →ₗ[ℝ] (I → E)) (feature : I → Γ → ℝ) (μ : FiniteLaw Γ) : Prop :=
  ∃ (D : E) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Γ),
    0 < H.weight 0 ∧
    (∀ n x, 0 < (kernel n).weight x) ∧
    (∀ n, (∑ x, (H.joint kernel).weight (n, x)) =
      ∑ x, (H.joint (fun _ => μ)).weight (n, x)) ∧
    HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom e atom n) D ∧
    ∀ i, HasSum (fun n => (H.weight n *
        ((kernel n).expect (feature i) - μ.expect (feature i))) •
      CarrierCoefficients.labeledAtom e atom n) (J D i)

namespace CarrierPolarization

variable [CompleteSpace E] [DecidableEq I] {Γ : Type*} [Fintype Γ]
  {e : E} {C M : ℝ} (P : CarrierPolarization E I e C M)

/-- The carrier exists for all sufficiently large n, assuming the concrete
polarization and vanishing ideal-increment bound. The finite moment-radius
result is invoked, and K is chosen internally from its positive radius. -/
theorem eventually_hasPositiveCarrier (hC : 0 ≤ C) (hM : 0 ≤ M) (he : ‖e‖ ≤ 1)
    (J : ℕ → E →ₗ[ℝ] (I → E)) (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hJ : ∀ n D, ‖J n D‖ ≤ δ n * ‖D‖)
    (feature : I → Γ → ℝ) (μ : FiniteLaw Γ) (hμ : ∀ x, 0 < μ.weight x)
    (R : MomentRightInverse feature) :
    ∀ᶠ n in atTop, HasPositiveCarrier e P.atom (J n) feature μ := by
  obtain ⟨radius, hpos, realize⟩ := exists_positive_moment_radius feature R μ hμ
  have hK : 0 < radius⁻¹ := inv_pos.mpr hpos
  filter_upwards [eventually_carrier_smallness δ hδ radius⁻¹ M C] with n hsmall
  obtain ⟨D, H, kernel, _, hzero, hkernel, hmarginal, hdensity, hmoment⟩ :=
    P.exists_positive_carrier (J n) (δ n) hC hM (hδ0 n) he (hJ n)
      feature μ hμ radius realize radius⁻¹ hK (by simp) hsmall.1 hsmall.2
  exact ⟨D, H, kernel, hzero, hkernel, hmarginal, hdensity, hmoment⟩

end CarrierPolarization

end CausalLowerbound.PartB
