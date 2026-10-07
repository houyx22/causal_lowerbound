import CausalLowerbound.PartC.SymmetricPropensityMatching
import CausalLowerbound.PartC.PhysicalTaperSeparation

/-! Retained likelihood matching for the actual symmetrized physical
carrier. Symmetry follows from its positive atom series. Separation of
the shared rough signs follows from the taper and a scale inequality;
when the taper vanishes, both sides vanish. The resulting perturbation
is precisely the physical assignment weight times the target effect. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative RoughPropensity
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {I G d : Type*} [Fintype I] [Fintype G] [Fintype d] [DecidableEq d]

set_option maxHeartbeats 600000 in
theorem carrier_propensity_retained_matching (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ)
    (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (k : d → ℤ)
    (c w N θ ja b t τ : ℝ) (hN : N ≠ 0) (hτ : 0 < τ)
    (hm : ∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y)
    (hscale : 2 * physicalChartDistanceConstant d * ℓ ≤ 4 * r * τ)
    (e : I ⊕ G ≃ Fin Q) (R T : I → ℝ) (offset : Fin Q → ℝ)
    (W : Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (H : DiscreteLaw ℕ)
    (hseries : HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom unit
      (pairedAtom reflection (naturalPhysicalAtom (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ)) n) W)
    (u : Fin Q × d → ℝ) :
    let keep : I → Fin Q := fun i => e (Sum.inl i)
    let sites := configurationSite u
    let x : Fin Q → d → ℝ := fun i => roughChartPoint x₀ r k (sites i)
    let B := remove (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) W
    let z := fun ζ i => normalizedRoughChart x₀ ℓ r h k c w N ζ (sites i)
    independentSigns.expect (fun ζ =>
      paperPhysicalPropensityPolynomial Q ρ x₀ r h k c w N ja t τ B u (z ζ) ζ
        (retainedPropensityPolynomial Q R T (fun _ => ja)
          (fun i => physicalRoughField x₀ ℓ h ζ (x (keep i))) (offset ∘ keep)
          (fun i => b * linearPartition (fun a => 4 * sites (keep i) a - 2)) (sites ∘ keep))) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        (paperCoefficientLaw Q).expect (fun ξ => independentSigns.expect (fun ζ =>
          pointValue (torusProjection u) (z ζ) ζ B *
            ((∏ i, (likelihood (R i) (T i) ja
              (offset (keep i) + b * rescaled (carriedProfile (paperCoefficientAtoms Q ρ ξ))
                (packetCenter x₀ r k) r (x (keep i))) (physicalRoughField x₀ ℓ h ζ (x (keep i))) +
              realField (R i) (T i) ja
                (assignmentWeight w x₀ r k (x (keep i)) * targetField x₀ h (ja * b * t) (x (keep i)))
                (physicalRoughField x₀ ℓ h ζ (x (keep i))))) -
              ∏ i, likelihood (R i) (T i) ja
                (offset (keep i) + b * rescaled (carriedProfile (paperCoefficientAtoms Q ρ ξ))
                  (packetCenter x₀ r k) r (x (keep i))) (physicalRoughField x₀ ℓ h ζ (x (keep i)))))) := by
  dsimp only
  by_cases hχ : graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) = 0
  · simp only [paperPhysicalPropensityPolynomial_eq_symmetric,
      symmetricPropensityCoefficientFunctional, propensityCoefficientFunctional,
      complete_graphTaper_permute, hχ, zero_smul, Finset.sum_const_zero, smul_zero,
      LinearMap.zero_apply, FiniteLaw.expect_const, zero_mul]
  · have hs := taper_nonzero_physical_separation x₀ ℓ r hr k u τ hτ hscale hχ
    have he := removed_physical_propensity_symmetric_retained_matching Q hQ (by simp)
      (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ) x₀ ℓ h hℓ hh
      (fun i => roughChartPoint x₀ r k (configurationSite u i)) hs e R T (fun _ => ja)
      (fun i => assignmentMultiplier c w (fun a => 4 * u (i, a) - 2) / N) offset
      (fun i => b * linearPartition (fun a => 4 * u (i, a) - 2)) W
      (carrier_series_value_symmetric x₀ ℓ r h k c w N θ H W hseries) u τ (t * N)
    dsimp only [Function.comp_def] at he
    have hshift (i : Fin Q) :
        ja * ((b * linearPartition (fun a => 4 * u (i, a) - 2)) * (t * N)) *
          (assignmentMultiplier c w (fun a => 4 * u (i, a) - 2) / N) *
            coarseBump x₀ h (roughChartPoint x₀ r k (configurationSite u i)) ^ 2 =
        assignmentWeight w x₀ r k (roughChartPoint x₀ r k (configurationSite u i)) *
          targetField x₀ h (ja * b * t) (roughChartPoint x₀ r k (configurationSite u i)) :=
      physical_propensity_shift_amplitude x₀ r h hr.ne' k c w N ja b t hN hm (configurationSite u i)
    simp only [hshift] at he
    have hκ : physicalPropensitySlotCorrection x₀ r h k c w N ja u =
        (fun i => (assignmentMultiplier c w (fun a => 4 * u (i, a) - 2) / N) ^ 2 * ja ^ 2 *
          (coarseBump x₀ h (roughChartPoint x₀ r k (configurationSite u i)) ^ 2) ^ 2) := by
      funext i
      exact physicalPropensitySlotCorrection_eq_variance x₀ r h k c w N ja u i
    simpa only [paperPhysicalPropensityPolynomial_eq_symmetric, hκ, normalizedRoughChart_eq_scale,
      carriedProfile_at_roughChart _ x₀ r hr.ne' k, Function.comp_def, configurationSite, mul_assoc] using he

end CausalLowerbound.PartC
