import CausalLowerbound.PartC.PhysicalPropensityPosterior

/-! An actual carrier realization with normalized retained-likelihood
identities for every q <= Q, using the same labels and coefficient kernel.
The original reflection, positivity, and symbol estimates are retained. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative RoughPropensity
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem HasPaperPropensityCarrier.likelihood_realization
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ ja t τ K δ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hcarr : HasPaperPropensityCarrier Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ) :
    let I := MomentExponent (CoefficientExponent d Q) (4 * Q)
    let L := ((Fintype.card I : ℝ) * polarizationBound (Fin Q) θ) * δ
    ∃ (B : Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (H : DiscreteLaw ℕ)
        (kernel : (activeBlocks (d := d) ℓ h → Bool) → ℕ →
          FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      reflection B = B ∧ ‖B‖ ≤ 2 ∧
      ‖B - unit‖ ≤ 2 * (K * ((1 + |θ|) ^ Q + 1) * (L + L)) ∧
      (∀ j : activeBlocks (d := d) ℓ h, ‖symbolPart j B‖ ≤ 2 * K * (L + L) *
        ((Q : ℝ) * ((θ / 2) * ((1 / N₀) * (ℓ / (2 * r)) ^ Fintype.card d)) * (1 + θ) ^ (Q - 1))) ∧
      0 < H.weight 0 ∧
      (∀ n, H.weight (PairedSeries.flipLabel n + 1) = H.weight (n + 1)) ∧
      (∀ ζ, kernel ζ 0 = paperCoefficientLaw Q) ∧ (∀ ζ n y, 0 < (kernel ζ n).weight y) ∧
      (∀ ζ n, (∑ y, (H.joint (kernel ζ)).weight (n, y)) = H.weight n) ∧
      HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom unit
        (pairedAtom reflection (naturalPhysicalAtom (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ)) n) B ∧
      ∀ (A G : Type) [Fintype A] [Fintype G] ζ (e : A ⊕ G ≃ Fin Q) (u : A → d → ℝ),
        (∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) →
        ∀ R T siteJa rough offset ψ : A → ℝ,
        (hcarr.posterior hθ1 H kernel ζ u).expect (fun ω => ∏ i,
          likelihood (R i) (T i) (siteJa i)
            (offset i + ψ i * coefficientEvaluation (paperCoefficientAtoms Q ρ ω) (u i)) (rough i)) -
          (paperCoefficientLaw Q).expect (fun ω => ∏ i,
            likelihood (R i) (T i) (siteJa i)
              (offset i + ψ i * coefficientEvaluation (paperCoefficientAtoms Q ρ ω) (u i)) (rough i)) =
          (carrierMarginal H
            (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) u)⁻¹ *
            ∫ z : G → d → ℝ,
              physicalPropensityIncrementValue Q ρ x₀ ℓ r h k c w N ja t τ B ζ
                (retainedPropensityPolynomial Q R T siteJa rough offset ψ u) (completedConfiguration e u z)
                  ∂Measure.pi (fun _ : G => cubeMeasure d) := by
  obtain ⟨B, H, kernel, href, hnorm, hball, hsymbol, hzero, hpair, hbase, hpos,
    hmarginal, hseries, _, _, hproject⟩ :=
      hcarr.projective_realization Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ hθ
  refine ⟨B, H, kernel, href, hnorm, hball, hsymbol, hzero, hpair, hbase, hpos,
    hmarginal, hseries, ?_⟩
  intro A G _ _ ζ e u hu R T siteJa rough offset ψ
  exact hcarr.likelihood_increment_of_projection hθ1 H kernel B ζ e u
    (hproject A G ζ e u hu) R T siteJa rough offset ψ

end CausalLowerbound.PartC
