import CausalLowerbound.PartC.PhysicalCarrierMarginals

/-! One actual propensity carrier, simultaneously for every retained
and ghost split. Both the full coefficient expectation and its increment
are integrated with the actual physical design density. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V] {D : ℕ}

def physicalCarrierValue (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (B : Representative.Array d V (activeBlocks (d := d) ℓ h) D)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (v : V × d → ℝ) : ℝ :=
  pointValue (torusProjection v)
    (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => v (j, a))) ζ B

def physicalPropensityIncrementValue (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ)
    (k : d → ℤ) (c w N ja t τ : ℝ)
    (B : Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (p : MvPolynomial (CoefficientExponent d Q) ℝ)
    (v : Fin Q × d → ℝ) : ℝ :=
  paperPhysicalPropensityPolynomial Q ρ x₀ r h k c w N ja t τ B v
    (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => v (j, a))) ζ p

set_option maxHeartbeats 1200000 in
theorem HasPaperPropensityCarrier.projective_realization
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ ja t τ K δ : ℝ) (hθ : 0 ≤ θ)
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
      (∀ (A G : Type) [Fintype A] [Fintype G] ζ (e : A ⊕ G ≃ Fin Q) (u : A → d → ℝ),
        (∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) →
        carrierMarginal H
          (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) u =
          ∫ z : G → d → ℝ, physicalCarrierValue x₀ ℓ r h k c w N B ζ (completedConfiguration e u z)
            ∂Measure.pi (fun _ : G => cubeMeasure d)) ∧
      (∀ (A G : Type) [Fintype A] [Fintype G] ζ (e : A ⊕ G ≃ Fin Q) (u : A → d → ℝ),
        (∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) →
        ∀ p : MvPolynomial (CoefficientExponent d Q) ℝ, p.totalDegree ≤ 4 * Q →
        weightedCarrierMarginal H
          (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
          (fun n => (kernel ζ n).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p)) u =
          ∫ z : G → d → ℝ,
            (paperCoefficientLaw Q).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p) *
              physicalCarrierValue x₀ ℓ r h k c w N B ζ (completedConfiguration e u z) +
            physicalPropensityIncrementValue Q ρ x₀ ℓ r h k c w N ja t τ B ζ p (completedConfiguration e u z)
            ∂Measure.pi (fun _ : G => cubeMeasure d)) ∧
      ∀ (A G : Type) [Fintype A] [Fintype G] ζ (e : A ⊕ G ≃ Fin Q) (u : A → d → ℝ),
        (∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) →
        ∀ p : MvPolynomial (CoefficientExponent d Q) ℝ, p.totalDegree ≤ 4 * Q →
        weightedCarrierMarginal H
          (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
          (fun n => (kernel ζ n).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p) -
            (paperCoefficientLaw Q).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p)) u =
          ∫ z : G → d → ℝ,
            physicalPropensityIncrementValue Q ρ x₀ ℓ r h k c w N ja t τ B ζ p (completedConfiguration e u z)
            ∂Measure.pi (fun _ : G => cubeMeasure d) := by
  rcases hcarr.2.2.2 with ⟨B, H, kernel, href, hnorm, hball, hsymbol, hzero, hpair,
    hbase, hpos, hmarginal, hseries, hdensity, hmoment⟩
  refine ⟨B, H, kernel, href, hnorm, hball, hsymbol, hzero, hpair, hbase, hpos,
    hmarginal, hseries, ?_, ?_, ?_⟩
  · intro A G _ _ ζ e u hu
    have he := hcarr.projective_hasSum hθ H ζ (fun _ => 1) 1 (by simp)
      (physicalCarrierValue x₀ ℓ r h k c w N B ζ)
      (fun v => by simpa only [physicalCarrierValue, mul_one] using hdensity ζ v) e u hu
    simpa only [weightedCarrierMarginal, carrierMarginal, mul_one] using he
  · intro A G _ _ ζ e u hu p hp
    let f := fun ω => eval (paperCoefficientAtoms Q ρ ω) p
    have hf (ω) : |f ω| ≤ ∑ y, |f y| :=
      Finset.single_le_sum (fun y _ => abs_nonneg (f y)) (Finset.mem_univ ω)
    apply hcarr.projective_hasSum hθ H ζ _ (∑ y, |f y|)
      (fun n => (kernel ζ n).abs_expect_le_bound f _ hf)
      (fun v => (paperCoefficientLaw Q).expect f * physicalCarrierValue x₀ ℓ r h k c w N B ζ v +
        physicalPropensityIncrementValue Q ρ x₀ ℓ r h k c w N ja t τ B ζ p v) _ e u hu
    intro v
    exact hasSum_weighted_expect (paperCoefficientLaw Q) (kernel ζ) H.weight _ _ _ _ (hdensity ζ v)
      (physical_propensity_polynomial_hasSum Q ρ x₀ ℓ r h k c w N θ ja t τ B H kernel ζ v
        (fun η => hmoment ζ η v) p hp)
  · intro A G _ _ ζ e u hu p hp
    let f := fun ω => eval (paperCoefficientAtoms Q ρ ω) p
    apply hcarr.projective_hasSum hθ H ζ _ (2 * ∑ y, |f y|)
      (coefficient_difference_bound (kernel ζ) (paperCoefficientLaw Q) f) _ _ e u hu
    intro v
    exact physical_propensity_polynomial_hasSum Q ρ x₀ ℓ r h k c w N θ ja t τ B H kernel ζ v
      (fun η => hmoment ζ η v) p hp

end CausalLowerbound.PartC
