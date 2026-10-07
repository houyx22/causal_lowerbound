import CausalLowerbound.PartC.SymmetricOutcomeMatching
import CausalLowerbound.PartC.PhysicalTaperSeparation
import CausalLowerbound.PartC.PhysicalOutcomeShift

/-! Cubic retained likelihood matching for the actual physical carrier.
The actual fourth-moment correction is used at every retained site.
Only sites with nonzero coarse envelope need assignment weights zero
or one; ghost sites have no assignment condition. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative RoughOutcome
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {I G d : Type*} [Fintype I] [Fintype G] [Fintype d] [DecidableEq d]

set_option maxHeartbeats 800000 in
theorem carrier_outcome_retained_matching (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ)
    (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (k : d → ℤ)
    (c w N θ a jb t τ : ℝ) (hN : N ≠ 0) (hτ : 0 < τ)
    (hm : ∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y)
    (hscale : 2 * physicalChartDistanceConstant d * ℓ ≤ 4 * r * τ)
    (e : I ⊕ G ≃ Fin Q) (R T : I → ℝ) (offset : Fin Q → ℝ)
    (W : Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (H : DiscreteLaw ℕ)
    (hseries : HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom unit
      (pairedAtom reflection (naturalPhysicalAtom (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ)) n) W)
    (u : Fin Q × d → ℝ)
    (hassign : ∀ i, coarseBump x₀ h (roughChartPoint x₀ r k (configurationSite u (e (Sum.inl i)))) ≠ 0 →
      assignmentWeight w x₀ r k (roughChartPoint x₀ r k (configurationSite u (e (Sum.inl i)))) = 0 ∨
      assignmentWeight w x₀ r k (roughChartPoint x₀ r k (configurationSite u (e (Sum.inl i)))) = 1) :
    let keep : I → Fin Q := fun i => e (Sum.inl i)
    let sites := configurationSite u
    let x : Fin Q → d → ℝ := fun i => roughChartPoint x₀ r k (sites i)
    let η := fun i => physicalRoughCorrection x₀ ℓ h (a * t) (x (keep i))
    let B := remove (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) W
    let z := fun ζ i => normalizedRoughChart x₀ ℓ r h k c w N ζ (sites i)
    independentSigns.expect (fun ζ =>
      paperPhysicalOutcomePolynomial Q ρ x₀ r h k c w N t τ B u (z ζ) ζ
        (retainedOutcomePolynomial Q R T (fun _ => jb) η
          (fun i => physicalRoughField x₀ ℓ h ζ (x (keep i))) (offset ∘ keep)
          (fun i => a * linearPartition (fun j => 4 * sites (keep i) j - 2)) (sites ∘ keep))) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        (paperCoefficientLaw Q).expect (fun ξ => independentSigns.expect (fun ζ =>
          pointValue (torusProjection u) (z ζ) ζ B *
            ((∏ i, (likelihood (R i) (T i) jb (η i)
              (offset (keep i) + a * rescaled (carriedProfile (paperCoefficientAtoms Q ρ ξ))
                (packetCenter x₀ r k) r (x (keep i))) (physicalRoughField x₀ ℓ h ζ (x (keep i))) +
              realField (R i) (T i)
                (offset (keep i) + a * rescaled (carriedProfile (paperCoefficientAtoms Q ρ ξ))
                  (packetCenter x₀ r k) r (x (keep i)))
                (assignmentWeight w x₀ r k (x (keep i)) * targetField x₀ h (a * t * jb) (x (keep i))))) -
              ∏ i, likelihood (R i) (T i) jb (η i)
                (offset (keep i) + a * rescaled (carriedProfile (paperCoefficientAtoms Q ρ ξ))
                  (packetCenter x₀ r k) r (x (keep i))) (physicalRoughField x₀ ℓ h ζ (x (keep i)))))) := by
  dsimp only
  by_cases hχ : graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) = 0
  · simp only [paperPhysicalOutcomePolynomial_eq_symmetric,
      symmetricOutcomeCoefficientFunctional, outcomeCoefficientFunctional,
      complete_graphTaper_permute, hχ, zero_smul, Finset.sum_const_zero, smul_zero,
      LinearMap.zero_apply, FiniteLaw.expect_const, zero_mul]
  · have hs := taper_nonzero_physical_separation x₀ ℓ r hr k u τ hτ hscale hχ
    have hshift (i : I) :
        coarseBump x₀ h (roughChartPoint x₀ r k (configurationSite u (e (Sum.inl i)))) = 0 ∨
        (a * linearPartition (fun j => 4 * u (e (Sum.inl i), j) - 2) * (t * N)) *
          (assignmentMultiplier c w (fun j => 4 * u (e (Sum.inl i), j) - 2) / N) = 0 ∨
        (a * linearPartition (fun j => 4 * u (e (Sum.inl i), j) - 2) * (t * N)) *
          (assignmentMultiplier c w (fun j => 4 * u (e (Sum.inl i), j) - 2) / N) = a * t := by
      by_cases hG : coarseBump x₀ h (roughChartPoint x₀ r k (configurationSite u (e (Sum.inl i)))) = 0
      · exact Or.inl hG
      · have hf := physical_outcome_shift_scale x₀ r hr.ne' k c w N a t hN hm (configurationSite u (e (Sum.inl i)))
        rcases hassign i hG with ha | ha
        · exact Or.inr (Or.inl (hf.trans (by rw [ha, mul_zero])))
        · exact Or.inr (Or.inr (hf.trans (by rw [ha, mul_one])))
    have he := removed_physical_outcome_symmetric_retained_matching Q hQ (by simp)
      (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ) x₀ ℓ h hℓ hh
      (fun i => roughChartPoint x₀ r k (configurationSite u i)) hs e R T (fun _ => a * t)
      (fun _ => jb) (fun i => assignmentMultiplier c w (fun j => 4 * u (i, j) - 2) / N) offset
      (fun i => a * linearPartition (fun j => 4 * u (i, j) - 2)) W
      (carrier_series_value_symmetric x₀ ℓ r h k c w N θ H W hseries) u τ (t * N) hshift
    dsimp only [Function.comp_def] at he
    have hδ (i : Fin Q) :
        ((a * linearPartition (fun j => 4 * u (i, j) - 2)) * (t * N)) *
          (assignmentMultiplier c w (fun j => 4 * u (i, j) - 2) / N) * jb *
            coarseBump x₀ h (roughChartPoint x₀ r k (configurationSite u i)) ^ 2 =
        assignmentWeight w x₀ r k (roughChartPoint x₀ r k (configurationSite u i)) *
          targetField x₀ h (a * t * jb) (roughChartPoint x₀ r k (configurationSite u i)) := by
      have hf := physical_outcome_shift_scale x₀ r hr.ne' k c w N a t hN hm (configurationSite u i)
      dsimp only [configurationSite] at hf
      rw [hf, targetField]
      ring
    simp only [hδ] at he
    simpa only [paperPhysicalOutcomePolynomial_eq_symmetric, normalizedRoughVariance, normalizedRoughChart_eq_scaled,
      carriedProfile_at_roughChart _ x₀ r hr.ne' k, Function.comp_def, configurationSite, mul_assoc] using he

end CausalLowerbound.PartC
