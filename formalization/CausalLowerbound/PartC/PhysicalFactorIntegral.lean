import CausalLowerbound.PartC.PhysicalRepresentativeAtoms

/-! The physical one-slot integral as an actual real linear functional on
all representative factors, for use in the full positive dictionary. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Representative

variable {d J : Type*} [Fintype d] [Fintype J] [DecidableEq J] {D : ℕ}

theorem factorValue_continuous {K : Type*} [TopologicalSpace K]
    (x : K → Wiener.Torus d) (hx : Continuous x) (z : K → ℝ) (hz : Continuous z)
    (ζ : J → Bool) (a : Factor d J D) : Continuous (fun u => factorValue (x u) (z u) ζ a) := by
  apply continuous_finset_sum
  intro r _
  exact ((hz.pow r.1.val).mul continuous_const).smul ((Wiener.toContinuous (a r)).continuous.comp hx)

variable [DecidableEq d]

theorem physicalFactor_integrable (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ) (hc : 0 < c)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (a : Factor d (activeBlocks (d := d) ℓ h) D) :
    IntegrableOn (fun u => (factorValue (Wiener.torusProjection u)
      (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ a).re) (Set.Icc (0 : d → ℝ) 1) :=
  (Complex.continuous_re.comp (factorValue_continuous _ Wiener.torusProjection_quotient.continuous _
    (normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ) ζ a)).continuousOn.integrableOn_compact isCompact_Icc

def physicalFactorIntegral (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ) (hc : 0 < c)
    (ζ : activeBlocks (d := d) ℓ h → Bool) : Factor d (activeBlocks (d := d) ℓ h) D →ₗ[ℝ] ℝ where
  toFun a := ∫ u in Set.Icc (0 : d → ℝ) 1, (factorValue (Wiener.torusProjection u)
    (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ a).re
  map_add' a b := by
    simp_rw [← factorEvaluation_apply, map_add, Complex.add_re, factorEvaluation_apply]
    exact integral_add (physicalFactor_integrable _ _ _ _ _ _ _ _ hc ζ a)
      (physicalFactor_integrable _ _ _ _ _ _ _ _ hc ζ b)
  map_smul' t a := by
    simp_rw [← factorEvaluation_apply, map_smul, factorEvaluation_apply]
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, RingHom.id_apply, smul_eq_mul]
    exact integral_const_mul t _

@[simp] theorem physicalFactorIntegral_unit (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ) (hc : 0 < c)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    physicalFactorIntegral x₀ ℓ r h k c w N hc ζ (factorUnit : Factor d (activeBlocks (d := d) ℓ h) D) = 1 := by
  simp [physicalFactorIntegral, factorUnit_value, setIntegral_const, measureReal_def, Real.volume_Icc_pi]

@[simp] theorem physicalFactorIntegral_centered (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ) (hc : 0 < c)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : Fin (D + 1)) (q : d → ℤ) (b : Bool) :
    physicalFactorIntegral x₀ ℓ r h k c w N hc ζ (physicalCenteredFactor x₀ ℓ r h k c w N e q b) = 0 :=
  physicalCenteredFactor_integral x₀ ℓ r h k c w N hc e q b ζ

end CausalLowerbound.PartC
