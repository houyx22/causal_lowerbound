import CausalLowerbound.UpperBound.BoundaryGeometry
import CausalLowerbound.UpperBound.StencilBias

/-! Physical placement of the tensor stencil, uniformly including boundary
targets.  The resulting nuisance contrast only uses local Hölder extensions
on an open set containing the closed unit cube. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def inwardReflectionL (x : d → ℝ) : (d → ℝ) →L[ℝ] (d → ℝ) where
  toFun := inwardReflection x
  map_add' := by intro u v; ext i; simp [inwardReflection, mul_add]
  map_smul' := by intro a u; ext i; simp [inwardReflection, mul_left_comm]
  cont := by unfold inwardReflection; fun_prop

omit [Fintype d] in
@[simp] theorem inwardReflectionL_apply (x u : d → ℝ) :
    inwardReflectionL x u = inwardReflection x u := rfl

theorem scaled_reflection_norm (x u : d → ℝ) (r : ℝ) :
    ‖(r • inwardReflectionL x) u‖ = |r| * ‖u‖ := by
  rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
    inwardReflectionL_apply, inwardReflection_norm]

omit [Fintype d] in
theorem inwardReflection_add (x u v : d → ℝ) :
    inwardReflection x (u + v) = inwardReflection x u + inwardReflection x v :=
  (inwardReflectionL x).map_add u v

def physicalAnchor (x₀ u : d → ℝ) (h : ℝ) : d → ℝ := inwardDisplace x₀ (h • u)

def physicalStencil (p : ℕ) (x₀ u : d → ℝ) (h ℓ r : ℝ)
    (z : TensorIndex d p → d → ℝ) (v : d → ℝ) :
    Option (Option (TensorIndex d p)) → d → ℝ :=
  fun i => physicalAnchor x₀ u h +
    (r • inwardReflectionL x₀) (tensorStencilNode p z ((ℓ / r) • v) i)

omit [Fintype d] in
theorem physicalStencil_anchor (p : ℕ) (x₀ u : d → ℝ) (h ℓ r : ℝ)
    (z : TensorIndex d p → d → ℝ) (v : d → ℝ) :
    physicalStencil p x₀ u h ℓ r z v (some none) = physicalAnchor x₀ u h := by
  simp only [physicalStencil, tensorStencilNode, Option.elim'_some, Option.elim'_none,
    map_zero, add_zero]

omit [Fintype d] in
theorem physicalStencil_auxiliary (p : ℕ) (x₀ u : d → ℝ) (h ℓ r : ℝ)
    (z : TensorIndex d p → d → ℝ) (v : d → ℝ) (j : TensorIndex d p) :
    physicalStencil p x₀ u h ℓ r z v (some (some j)) =
      inwardDisplace x₀ (h • u + r • z j) := by
  simp only [physicalStencil, tensorStencilNode, Option.elim'_some, physicalAnchor,
    inwardDisplace_add, ContinuousLinearMap.smul_apply, inwardReflectionL_apply,
    inwardReflection_smul]

omit [Fintype d] in
theorem physicalStencil_partner (p : ℕ) (x₀ u : d → ℝ) (h ℓ r : ℝ) (hr : r ≠ 0)
    (z : TensorIndex d p → d → ℝ) (v : d → ℝ) :
    physicalStencil p x₀ u h ℓ r z v none = inwardDisplace x₀ (h • u + ℓ • v) := by
  simp only [physicalStencil, tensorStencilNode, Option.elim'_none, physicalAnchor,
    inwardDisplace_add, ContinuousLinearMap.smul_apply, inwardReflectionL_apply,
    inwardReflection_smul, smul_smul]
  rw [show r * (ℓ / r) = ℓ by field_simp]

theorem nonnegative_coordinate_norm_le {v : d → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ R) : ‖v‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hv i).1]
  exact (hv i).2

theorem physicalStencil_geometry (p : ℕ) (T : StencilTemplate d p)
    (x₀ u : d → ℝ) {h ℓ r : ℝ} (z : TensorIndex d p → d → ℝ) (v : d → ℝ)
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1 / 4)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (hz : ∀ j, z j ∈ T.box j)
    (i : Option (Option (TensorIndex d p))) :
    (∀ a, 0 ≤ physicalStencil p x₀ u h ℓ r z v i a ∧
      physicalStencil p x₀ u h ℓ r z v i a ≤ 1) ∧
      ‖physicalStencil p x₀ u h ℓ r z v i - x₀‖ ≤ h := by
  have hr : 0 < r := hℓ.trans_le hℓr
  cases i with
  | none =>
      rw [physicalStencil_partner p x₀ u h ℓ r hr.ne' z v]
      exact twoScale_point_geometry x₀ u v hx hh hhsmall hℓ.le (hℓr.trans hrh) hu hv
  | some i =>
      cases i with
      | none =>
          rw [physicalStencil_anchor]
          have he := twoScale_point_geometry x₀ u (0 : d → ℝ) hx hh hhsmall
            (show (0 : ℝ) ≤ 0 by rfl) (by linarith : (0 : ℝ) ≤ h / 4) hu
            (fun _ => by norm_num)
          simpa only [zero_smul, add_zero, physicalAnchor] using he
      | some j =>
          rw [physicalStencil_auxiliary]
          exact twoScale_point_geometry x₀ u (z j) hx hh hhsmall hr.le hrh hu
            (fun a => ⟨(T.box_positive j (hz j) a).1.le, (T.box_positive j (hz j) a).2.le⟩)

theorem physicalStencil_contrast_bound (p q : ℕ) (hqp : q ≤ p)
    (T : StencilTemplate d p) (x₀ u : d → ℝ) {h ℓ r C θ : ℝ}
    (z : TensorIndex d p → d → ℝ) (v : d → ℝ)
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1 / 4)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (hz : ∀ j, z j ∈ T.box j)
    (f : (d → ℝ) → ℝ) {U : Set (d → ℝ)} (hU : IsOpen U)
    (hcube : Icc (0 : d → ℝ) 1 ⊆ U)
    (hf : ContDiffOn ℝ q f U) (hholder : HolderControlOn q θ C f U)
    (hC : 0 ≤ C) (hθ : 0 ≤ θ) :
    |∑ i, tensorContrastWeights p z ((ℓ / r) • v) i *
      f (physicalStencil p x₀ u h ℓ r z v i)| ≤
      C * (1 + Fintype.card (TensorIndex d p) * T.inverseBound) *
        twoScaleModulus ((q : ℝ) + θ) ℓ r := by
  have hr : 0 < r := hℓ.trans_le hℓr
  have hη : 0 ≤ ℓ / r := div_nonneg hℓ.le hr.le
  have hvnorm : ‖v‖ ≤ 1 := nonnegative_coordinate_norm_le zero_le_one hv
  have hgeom := physicalStencil_geometry p T x₀ u z v hx hh hhsmall hℓ hℓr hrh hu hv hz
  have hnodes (i : Option (Option (TensorIndex d p))) :
      physicalStencil p x₀ u h ℓ r z v i ∈ Icc (0 : d → ℝ) 1 :=
    ⟨fun a => ((hgeom i).1 a).1, fun a => ((hgeom i).1 a).2⟩
  have hanchor : physicalAnchor x₀ u h ∈ Icc (0 : d → ℝ) 1 := by
    simpa only [physicalStencil_anchor] using hnodes (some none)
  apply tensor_stencil_contrast_bound p q hqp T z ((ℓ / r) • v) hz hC hθ hℓ hℓr
  · intro i
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hη,
      abs_of_nonneg (hv i).1]
    exact (mul_le_mul_of_nonneg_left (hv i).2 hη).trans_eq (mul_one _)
  · exact hU
  · exact hf
  · exact hholder
  · intro i t ht
    have hconv : Convex ℝ (Icc (0 : d → ℝ) 1) := by
      rw [← pi_univ_Icc]
      exact convex_pi (fun _ _ => convex_Icc (𝕜 := ℝ) 0 1)
    have he := hconv.add_smul_sub_mem
      hanchor (hnodes i) ht
    apply hcube
    simpa only [physicalStencil, add_sub_cancel_left] using he
  · rw [scaled_reflection_norm, abs_of_pos hr, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    calc
      r * (ℓ / r * ‖v‖) ≤ r * (ℓ / r * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvnorm hη) hr.le
      _ = ℓ := by field_simp
  · intro j
    rw [scaled_reflection_norm, abs_of_pos hr]
    apply (mul_le_mul_of_nonneg_left _ hr.le).trans_eq (mul_one r)
    exact nonnegative_coordinate_norm_le zero_le_one
      (fun a => ⟨(T.box_positive j (hz j) a).1.le, (T.box_positive j (hz j) a).2.le⟩)

end CausalLowerbound.UpperBound
