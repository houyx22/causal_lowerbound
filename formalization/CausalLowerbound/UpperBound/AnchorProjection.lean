import CausalLowerbound.UpperBound.KernelVariance
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The anchor marginal of Lebesgue measure on the accepted stencil.
Integrating out all other roles leaves a constant multiple of Lebesgue
measure on the fixed anchor box, uniformly under boundary reflection. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open CausalLowerbound.PartB.ShellGeometry
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

theorem inwardReflection_measurePreserving (x₀ : d → ℝ) :
    MeasurePreserving (inwardReflection x₀) volume volume := by
  apply measurePreserving_pi (fun _ : d => (volume : Measure ℝ)) (fun _ : d => (volume : Measure ℝ))
  intro i
  by_cases hi : x₀ i ≤ 1 / 2
  · convert (MeasurePreserving.id (volume : Measure ℝ)) using 1
    ext u
    simp only [inwardSign, if_pos hi, one_mul, id_eq]
  · convert (Measure.measurePreserving_neg (volume : Measure ℝ)) using 1
    ext u
    simp only [inwardSign, if_neg hi, neg_one_mul]

theorem normalizedDisplacement_measurable (x₀ origin : d → ℝ) (h : ℝ) :
    Measurable (fun y => normalizedDisplacement x₀ origin y h) := by
  unfold normalizedDisplacement inwardReflection
  fun_prop

theorem normalizedDisplacement_map_volume (x₀ origin : d → ℝ) {h : ℝ} (hh : 0 < h) :
    volume.map (fun y => normalizedDisplacement x₀ origin y h) =
      (ENNReal.ofReal h ^ Fintype.card d) • (volume : Measure (d → ℝ)) := by
  have hs : MeasurePreserving (fun y : d → ℝ => y - origin) volume volume := by
    simpa only [sub_eq_add_neg] using (measurePreserving_add_right (volume : Measure (d → ℝ)) (-origin))
  have hg := (inwardReflection_measurePreserving x₀).comp hs
  have he : (fun y => normalizedDisplacement x₀ origin y h) =
      (fun u : d → ℝ => h⁻¹ • u) ∘ (inwardReflection x₀ ∘ (fun y => y - origin)) := rfl
  rw [he, ← Measure.map_map (by fun_prop) hg.measurable, hg.map_eq,
    Measure.map_addHaar_smul volume (inv_ne_zero hh.ne')]
  simp only [inv_pow, inv_inv, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, abs_of_nonneg (pow_nonneg hh.le _), ENNReal.ofReal_pow hh.le]

theorem anchorUnitBox_eq_coordinateBox :
    anchorUnitBox d = coordinateBox (fun _ : d => 1 / 8) (1 / 8) := by
  norm_num [anchorUnitBox, coordinateBox]
  rfl

theorem normalizedDisplacement_anchor_preimage (x₀ origin : d → ℝ) {h : ℝ} (hh : 0 < h) :
    (fun y => normalizedDisplacement x₀ origin y h) ⁻¹' anchorUnitBox d =
      coordinateBox (origin + h • inwardReflection x₀ (fun _ => 1 / 8)) (h / 8) := by
  ext y
  rw [Set.mem_preimage, anchorUnitBox_eq_coordinateBox,
    normalizedDisplacement_mem_box x₀ origin y _ hh, mul_one_div]

theorem acceptedStencil_anchor_restriction (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r) (E : Set (d → ℝ)) :
    observedAnchorCoordinate p x₀ h ⁻¹' E ∩ acceptedStencil p T x₀ h ℓ r =
      stencilAnchorSplit p ⁻¹' mixedCluster
        ((fun y => normalizedDisplacement x₀ x₀ y h) ⁻¹' (E ∩ anchorUnitBox d))
        (stencilPhysicalShift p x₀ ℓ r) (stencilPhysicalRadius p T ℓ r) := by
  rw [acceptedStencil_eq_mixedCluster p T x₀ hh hℓ hr,
    Set.preimage_inter, normalizedDisplacement_anchor_preimage x₀ x₀ hh]
  ext X
  simp only [Set.mem_inter_iff, Set.mem_preimage, mixedCluster, Set.mem_setOf_eq,
    stencilAnchorSplit, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, observedAnchorCoordinate]
  tauto

theorem acceptedStencil_anchor_map_volume (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r) :
    (volume.restrict (acceptedStencil p T x₀ h ℓ r)).map (observedAnchorCoordinate p x₀ h) =
      (ENNReal.ofReal h ^ Fintype.card d * ENNReal.ofReal ℓ ^ Fintype.card d *
        ENNReal.ofReal (2 * r * T.radius) ^ (Fintype.card (TensorIndex d p) * Fintype.card d)) •
        volume.restrict (anchorUnitBox d) := by
  have hbox : MeasurableSet (anchorUnitBox d) := measurableSet_Icc
  ext E hE
  rw [Measure.map_apply (continuous_observedAnchorCoordinate p x₀ h).measurable hE,
    Measure.restrict_apply (hE.preimage (continuous_observedAnchorCoordinate p x₀ h).measurable),
    acceptedStencil_anchor_restriction p T x₀ hh hℓ hr E,
    (stencilAnchorSplit_volume_preserving (d := d) p).measure_preimage_equiv,
    mixedCluster_volume _ ((hE.inter hbox).preimage
      (normalizedDisplacement_measurable x₀ x₀ h)),
    ← Measure.map_apply (normalizedDisplacement_measurable x₀ x₀ h) (hE.inter hbox),
    normalizedDisplacement_map_volume x₀ x₀ hh,
    Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply hE,
    Fintype.prod_option]
  simp only [stencilPhysicalRadius, Option.elim'_none, Option.elim'_some,
    Finset.prod_const, Finset.card_univ, ← pow_mul, ENNReal.smul_def, smul_eq_mul]
  rw [show (2 : ℝ) * (ℓ / 2) = ℓ by ring,
    show (2 : ℝ) * (r * T.radius) = 2 * r * T.radius by ring]
  ring

theorem acceptedStencil_anchor_integral (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (f : (d → ℝ) → ℝ) (hf : Measurable f) :
    (∫ X in acceptedStencil p T x₀ h ℓ r, f (observedAnchorCoordinate p x₀ h X)) =
      (4 : ℝ) ^ Fintype.card d * stencilMass p T h ℓ r * ∫ u in anchorUnitBox d, f u := by
  have hδ := T.radius_pos
  have hmp : MeasurePreserving (observedAnchorCoordinate p x₀ h)
      (volume.restrict (acceptedStencil p T x₀ h ℓ r))
      ((ENNReal.ofReal h ^ Fintype.card d * ENNReal.ofReal ℓ ^ Fintype.card d *
        ENNReal.ofReal (2 * r * T.radius) ^ (Fintype.card (TensorIndex d p) * Fintype.card d)) •
        volume.restrict (anchorUnitBox d)) :=
    ⟨(continuous_observedAnchorCoordinate p x₀ h).measurable,
      acceptedStencil_anchor_map_volume p T x₀ hh hℓ hr⟩
  rw [integral_comp_measurePreserving hmp hf.aestronglyMeasurable, integral_smul_measure]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hh.le,
    ENNReal.toReal_ofReal hℓ.le, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r * T.radius), smul_eq_mul]
  have hc : Fintype.card (StencilRole d p) - 2 = Fintype.card (TensorIndex d p) := by
    simp only [StencilRole, Fintype.card_option]
    omega
  rw [stencilMass, fineCellVolume_toReal hℓ.le, coarseCellVolume_toReal p T hr.le, hc]
  congr 1
  simp only [div_pow, pow_mul]
  field_simp
  ring

theorem acceptedStencil_anchor_energy (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (θ : TensorIndex d p → ℝ) :
    (∫ X in acceptedStencil p T x₀ h ℓ r, tensorPolynomial p θ (observedAnchorCoordinate p x₀ h X) ^ 2) =
      (4 : ℝ) ^ Fintype.card d * stencilMass p T h ℓ r * tensorGramEnergy p θ := by
  rw [acceptedStencil_anchor_integral p T x₀ hh hℓ hr _
    ((continuous_tensorPolynomial p θ).pow 2).measurable, tensorGramEnergy_eq_integral]

end CausalLowerbound.UpperBound
