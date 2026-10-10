import CausalLowerbound.UpperBound.ObservedStencil
import CausalLowerbound.UpperBound.MixedClusterVolume

/-! The accepted event in observed coordinates is an ordinary mixed-scale
cluster.  Its exact Lebesgue volume includes all boundary reflections. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open CausalLowerbound.PartB.ShellGeometry
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

theorem normalizedDisplacement_mem_box (x₀ origin y c : d → ℝ) {r R : ℝ} (hr : 0 < r) :
    normalizedDisplacement x₀ origin y r ∈ coordinateBox c R ↔
      y ∈ coordinateBox (origin + r • inwardReflection x₀ c) (r * R) := by
  have hd : y - (origin + r • inwardReflection x₀ c) =
      r • inwardReflection x₀ (normalizedDisplacement x₀ origin y r - c) := by
    have he := normalizedDisplacement_reconstruct x₀ origin y r hr.ne'
    change _ = r • ((inwardReflectionL x₀) (normalizedDisplacement x₀ origin y r - c))
    rw [map_sub, smul_sub]
    change y - (origin + r • inwardReflection x₀ c) =
      r • inwardReflection x₀ (normalizedDisplacement x₀ origin y r) -
        r • inwardReflection x₀ c
    rw [eq_sub_of_add_eq' he]
    abel
  rw [mem_coordinateBox, mem_coordinateBox]
  apply forall_congr'
  intro i
  have ha := congrArg abs (congrFun hd i)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, inwardReflection, abs_mul,
    inwardSign_abs, mul_one, one_mul, abs_of_pos hr] at ha
  rw [ha]
  exact (mul_le_mul_left hr).symm

def stencilAnchorSplit (p : ℕ) :
    (StencilRole d p → d → ℝ) ≃ᵐ ((d → ℝ) × (Option (TensorIndex d p) → d → ℝ)) where
  toFun X := (X (some none), Option.elim' (X none) (fun j => X (some (some j))))
  invFun z := Option.elim' (z.2 none) (Option.elim' z.1 (fun j => z.2 (some j)))
  left_inv := by intro X; funext i; cases i with
    | none => rfl
    | some i => cases i <;> rfl
  right_inv := by intro z; apply Prod.ext; rfl; funext i; cases i <;> rfl
  measurable_toFun := by
    apply (measurable_pi_apply _).prodMk
    apply measurable_pi_lambda
    intro i
    cases i <;> exact measurable_pi_apply _
  measurable_invFun := by
    change Measurable (fun z : (d → ℝ) × (Option (TensorIndex d p) → d → ℝ) =>
      Option.elim' (z.2 none) (Option.elim' z.1 (fun j => z.2 (some j))))
    apply measurable_pi_lambda
    intro i
    cases i with
    | none =>
        change Measurable (fun z : (d → ℝ) × (Option (TensorIndex d p) → d → ℝ) => z.2 none)
        exact (measurable_pi_apply _).comp measurable_snd
    | some i => cases i with
      | none => exact measurable_fst
      | some j =>
          change Measurable (fun z : (d → ℝ) × (Option (TensorIndex d p) → d → ℝ) => z.2 (some j))
          exact (measurable_pi_apply _).comp measurable_snd

theorem stencilAnchorSplit_volume_preserving (p : ℕ) :
    MeasurePreserving (stencilAnchorSplit (d := d) p) volume volume := by
  suffices hs : MeasurePreserving (stencilAnchorSplit (d := d) p).symm volume volume from hs.symm
  refine ⟨(stencilAnchorSplit p).symm.measurable, ?_⟩
  change (volume.map (stencilAnchorSplit (d := d) p).symm) = Measure.pi (fun _ => volume)
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [Measure.map_apply (stencilAnchorSplit p).symm.measurable (MeasurableSet.univ_pi hs)]
  have he : (stencilAnchorSplit (d := d) p).symm ⁻¹' Set.univ.pi s =
      s (some none) ×ˢ Set.univ.pi (Option.elim' (s none) (fun j => s (some (some j)))) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      exact ⟨h (some none), fun i => by cases i <;> exact h _⟩
    · rintro ⟨ha, hr⟩ i
      cases i with
      | none => exact hr none
      | some i => cases i with
        | none => exact ha
        | some j => exact hr (some j)
  rw [he, Measure.volume_eq_prod, Measure.prod_prod]
  change volume (s (some none)) *
    (Measure.pi (fun _ : Option (TensorIndex d p) => (volume : Measure (d → ℝ))))
      (Set.univ.pi (Option.elim' (s none) (fun j => s (some (some j))))) = _
  rw [Measure.pi_pi, Fintype.prod_option, Fintype.prod_option, Fintype.prod_option]
  simp only [Option.elim'_none, Option.elim'_some]
  ring

def stencilPhysicalShift (p : ℕ) (x₀ : d → ℝ) (ℓ r : ℝ) :
    Option (TensorIndex d p) → d → ℝ :=
  Option.elim' (ℓ • inwardReflection x₀ (fun _ => 1 / 2))
    (fun j => r • inwardReflection x₀ (gridNode p j))

def stencilPhysicalRadius (p : ℕ) (T : StencilTemplate d p) (ℓ r : ℝ) :
    Option (TensorIndex d p) → ℝ := Option.elim' (ℓ / 2) (fun _ => r * T.radius)

theorem acceptedStencil_eq_mixedCluster (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r) :
    acceptedStencil p T x₀ h ℓ r = stencilAnchorSplit p ⁻¹'
      mixedCluster (coordinateBox (x₀ + h • inwardReflection x₀ (fun _ => 1 / 8)) (h / 8))
        (stencilPhysicalShift p x₀ ℓ r) (stencilPhysicalRadius p T ℓ r) := by
  have hanchor : anchorUnitBox d = coordinateBox (fun _ : d => 1 / 8) (1 / 8) := by
    norm_num [anchorUnitBox, coordinateBox]
    rfl
  have hpartner : Icc (0 : d → ℝ) 1 = coordinateBox (fun _ : d => 1 / 2) (1 / 2) := by
    norm_num [coordinateBox]
    rfl
  ext X
  simp only [acceptedStencil, Set.mem_setOf_eq, hanchor, hpartner,
    observedAnchorCoordinate, observedPartnerCoordinate, observedAuxiliaryCoordinates,
    StencilTemplate.box, normalizedDisplacement_mem_box x₀ _ _ _ hh,
    normalizedDisplacement_mem_box x₀ _ _ _ hℓ,
    normalizedDisplacement_mem_box x₀ _ _ _ hr]
  simp only [Set.mem_preimage, mixedCluster, Set.mem_setOf_eq, stencilAnchorSplit,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, stencilPhysicalShift, stencilPhysicalRadius,
    Option.forall, Option.elim'_none, Option.elim'_some, mul_one_div]

theorem acceptedStencil_volume (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r) :
    volume (acceptedStencil p T x₀ h ℓ r) =
      ENNReal.ofReal (h / 4) ^ Fintype.card d *
        (ENNReal.ofReal ℓ ^ Fintype.card d *
          ENNReal.ofReal (2 * r * T.radius) ^
            (Fintype.card (TensorIndex d p) * Fintype.card d)) := by
  rw [acceptedStencil_eq_mixedCluster p T x₀ hh hℓ hr,
    (stencilAnchorSplit_volume_preserving (d := d) p).measure_preimage_equiv,
    mixedCluster_volume_box]
  rw [Fintype.prod_option]
  simp only [stencilPhysicalRadius, Option.elim'_none, Option.elim'_some,
    Finset.prod_const, Finset.card_univ, ← pow_mul]
  congr 2 <;> congr 1 <;> ring

end CausalLowerbound.UpperBound
