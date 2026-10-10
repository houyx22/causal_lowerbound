import CausalLowerbound.UpperBound.InwardStencil
import CausalLowerbound.UpperBound.MeasurableStencil
import CausalLowerbound.UpperBound.PolynomialGram

/-! Measurable acceptance and weights from the observed covariates.
On acceptance the observations reconstruct the physical inward stencil,
so the deterministic Hölder contrast bound applies to actual data. -/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

abbrev StencilRole (d : Type*) (p : ℕ) := Option (Option (TensorIndex d p))

def normalizedDisplacement (x₀ origin y : d → ℝ) (r : ℝ) : d → ℝ :=
  r⁻¹ • inwardReflection x₀ (y - origin)

omit [Fintype d] in
theorem normalizedDisplacement_reconstruct (x₀ origin y : d → ℝ) (r : ℝ) (hr : r ≠ 0) :
    origin + r • inwardReflection x₀ (normalizedDisplacement x₀ origin y r) = y := by
  rw [normalizedDisplacement, inwardReflection_smul, inwardReflection_involutive,
    smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]

def observedAnchorCoordinate (p : ℕ) (x₀ : d → ℝ) (h : ℝ)
    (X : StencilRole d p → d → ℝ) : d → ℝ :=
  normalizedDisplacement x₀ x₀ (X (some none)) h

def observedPartnerCoordinate (p : ℕ) (x₀ : d → ℝ) (ℓ : ℝ)
    (X : StencilRole d p → d → ℝ) : d → ℝ :=
  normalizedDisplacement x₀ (X (some none)) (X none) ℓ

def observedAuxiliaryCoordinates (p : ℕ) (x₀ : d → ℝ) (r : ℝ)
    (X : StencilRole d p → d → ℝ) : TensorIndex d p → d → ℝ :=
  fun j => normalizedDisplacement x₀ (X (some none)) (X (some (some j))) r

def acceptedStencil (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ) :
    Set (StencilRole d p → d → ℝ) :=
  {X | observedAnchorCoordinate p x₀ h X ∈ anchorUnitBox d ∧
    observedPartnerCoordinate p x₀ ℓ X ∈ Icc (0 : d → ℝ) 1 ∧
    ∀ j, observedAuxiliaryCoordinates p x₀ r X j ∈ T.box j}

def observedStencilWeights (p : ℕ) (x₀ : d → ℝ) (ℓ r : ℝ)
    (X : StencilRole d p → d → ℝ) : StencilRole d p → ℝ :=
  tensorContrastWeights p (observedAuxiliaryCoordinates p x₀ r X)
    ((ℓ / r) • observedPartnerCoordinate p x₀ ℓ X)

omit [Fintype d] in
theorem continuous_observedAnchorCoordinate (p : ℕ) (x₀ : d → ℝ) (h : ℝ) :
    Continuous (observedAnchorCoordinate p x₀ h) := by
  unfold observedAnchorCoordinate normalizedDisplacement inwardReflection
  fun_prop

omit [Fintype d] in
theorem continuous_observedPartnerCoordinate (p : ℕ) (x₀ : d → ℝ) (ℓ : ℝ) :
    Continuous (observedPartnerCoordinate p x₀ ℓ) := by
  unfold observedPartnerCoordinate normalizedDisplacement inwardReflection
  fun_prop

omit [Fintype d] in
theorem continuous_observedAuxiliaryCoordinates (p : ℕ) (x₀ : d → ℝ) (r : ℝ) :
    Continuous (observedAuxiliaryCoordinates p x₀ r) := by
  unfold observedAuxiliaryCoordinates normalizedDisplacement inwardReflection
  fun_prop

theorem acceptedStencil_measurable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) : MeasurableSet (acceptedStencil p T x₀ h ℓ r) := by
  simp only [acceptedStencil, Set.setOf_and, Set.setOf_forall]
  apply MeasurableSet.inter
    (measurableSet_Icc.preimage (continuous_observedAnchorCoordinate p x₀ h).measurable)
  apply MeasurableSet.inter
    (measurableSet_Icc.preimage (continuous_observedPartnerCoordinate p x₀ ℓ).measurable)
  exact MeasurableSet.iInter (fun j => (T.box_measurable j).preimage
    (((continuous_apply j).comp (continuous_observedAuxiliaryCoordinates p x₀ r)).measurable))

theorem observedStencilWeights_measurable (p : ℕ) (x₀ : d → ℝ) (ℓ r : ℝ) :
    Measurable (observedStencilWeights p x₀ ℓ r) := by
  unfold observedStencilWeights
  have hw := measurable_tensorContrastWeights_comp (d := d) p (observedAuxiliaryCoordinates p x₀ r)
    (fun X => (ℓ / r) • observedPartnerCoordinate p x₀ ℓ X)
    (continuous_observedAuxiliaryCoordinates p x₀ r).measurable
    ((continuous_observedPartnerCoordinate p x₀ ℓ).const_smul (ℓ / r)).measurable
  exact hw

omit [Fintype d] in
theorem observedAnchor_reconstruct (p : ℕ) (x₀ : d → ℝ) (h : ℝ) (hh : h ≠ 0)
    (X : StencilRole d p → d → ℝ) :
    physicalAnchor x₀ (observedAnchorCoordinate p x₀ h X) h = X (some none) := by
  unfold physicalAnchor inwardDisplace
  rw [inwardReflection_smul]
  exact normalizedDisplacement_reconstruct x₀ x₀ _ h hh

omit [Fintype d] in
theorem observedStencil_reconstruct (p : ℕ) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (hh : h ≠ 0) (hℓ : ℓ ≠ 0) (hr : r ≠ 0) (X : StencilRole d p → d → ℝ) :
    physicalStencil p x₀ (observedAnchorCoordinate p x₀ h X) h ℓ r
      (observedAuxiliaryCoordinates p x₀ r X) (observedPartnerCoordinate p x₀ ℓ X) = X := by
  funext i
  cases i with
  | none =>
      simp only [physicalStencil, tensorStencilNode, Option.elim'_none,
        observedAnchor_reconstruct p x₀ h hh X, ContinuousLinearMap.smul_apply,
        inwardReflectionL_apply, inwardReflection_smul, smul_smul]
      rw [show r * (ℓ / r) = ℓ by field_simp]
      exact normalizedDisplacement_reconstruct x₀ _ _ ℓ hℓ
  | some i =>
      cases i with
      | none => rw [physicalStencil_anchor, observedAnchor_reconstruct p x₀ h hh X]
      | some j =>
          simp only [physicalStencil, tensorStencilNode, Option.elim'_some,
            observedAnchor_reconstruct p x₀ h hh X, ContinuousLinearMap.smul_apply,
            inwardReflectionL_apply]
          exact normalizedDisplacement_reconstruct x₀ _ _ r hr

theorem acceptedStencil_contrast_bound (p q : ℕ) (hqp : q ≤ p)
    (T : StencilTemplate d p) (x₀ : d → ℝ) {h ℓ r C θ : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (X : StencilRole d p → d → ℝ) (hX : X ∈ acceptedStencil p T x₀ h ℓ r)
    (f : (d → ℝ) → ℝ) {U : Set (d → ℝ)} (hU : IsOpen U)
    (hcube : Icc (0 : d → ℝ) 1 ⊆ U)
    (hf : ContDiffOn ℝ q f U) (hholder : HolderControlOn q θ C f U)
    (hC : 0 ≤ C) (hθ : 0 ≤ θ) :
    |∑ i, observedStencilWeights p x₀ ℓ r X i * f (X i)| ≤
      C * (1 + Fintype.card (TensorIndex d p) * T.inverseBound) *
        twoScaleModulus ((q : ℝ) + θ) ℓ r := by
  have he := physicalStencil_contrast_bound p q hqp T x₀
    (observedAnchorCoordinate p x₀ h X) (observedAuxiliaryCoordinates p x₀ r X)
    (observedPartnerCoordinate p x₀ ℓ X) hx hh hhsmall hℓ hℓr hrh
    (fun i => ⟨hX.1.1 i, hX.1.2 i⟩)
    (fun i => ⟨hX.2.1.1 i, hX.2.1.2 i⟩) hX.2.2 f hU hcube hf hholder hC hθ
  rw [observedStencil_reconstruct p x₀ h ℓ r hh.ne' hℓ.ne' (hℓ.trans_le hℓr).ne' X] at he
  exact he

end CausalLowerbound.UpperBound
