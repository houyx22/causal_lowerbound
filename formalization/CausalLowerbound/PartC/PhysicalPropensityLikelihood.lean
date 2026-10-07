import CausalLowerbound.PartC.PropensityLikelihoodPolynomials

/-! The actual positive carrier applied to full likelihood polynomials,
including the baseline term. The same countable law and sign-dependent
kernel work for every polynomial of degree at most 4Q. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial RoughPropensity
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem hasSum_weighted_expect {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (kernel : ℕ → FiniteLaw Ω) (weight density : ℕ → ℝ)
    (f : Ω → ℝ) (mass correction : ℝ)
    (hd : HasSum (fun n => weight n * density n) mass)
    (hm : HasSum (fun n => (weight n * ((kernel n).expect f - μ.expect f)) * density n) correction) :
    HasSum (fun n => (weight n * (kernel n).expect f) * density n)
      (μ.expect f * mass + correction) := by
  have hs := (hd.mul_left (μ.expect f)).add hm
  convert hs using 1
  ext n
  ring

theorem HasPaperPropensityCarrier.polynomial_realization
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ ja t τ K δ : ℝ)
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
      (∀ ζ (u : UnitChart (Fin Q × d)), HasSum (fun n => H.weight n *
        ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ (fun a => u.val (j, a)))
        (pointValue (torusProjection u.val)
          (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u.val (j, a))) ζ B)) ∧
      ∀ ζ (u : UnitChart (Fin Q × d)) (p : MvPolynomial (CoefficientExponent d Q) ℝ),
        p.totalDegree ≤ 4 * Q →
        HasSum (fun n => (H.weight n * (kernel ζ n).expect
          (fun ω => eval (paperCoefficientAtoms Q ρ ω) p)) *
            ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ (fun a => u.val (j, a)))
          ((paperCoefficientLaw Q).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p) *
            pointValue (torusProjection u.val)
              (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u.val (j, a))) ζ B +
            paperPhysicalPropensityPolynomial Q ρ x₀ r h k c w N ja t τ B u.val
              (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u.val (j, a))) ζ p) := by
  rcases hcarr.2.2.2 with ⟨B, H, kernel, href, hnorm, hball, hsymbol, hzero, hpair,
    hbase, hpos, hmarginal, hseries, hdensity, hmoment⟩
  refine ⟨B, H, kernel, href, hnorm, hball, hsymbol, hzero, hpair, hbase, hpos,
    hmarginal, hseries, hdensity, ?_⟩
  intro ζ u p hp
  exact hasSum_weighted_expect (paperCoefficientLaw Q) (kernel ζ) H.weight _ _ _ _ (hdensity ζ u)
    (physical_propensity_polynomial_hasSum Q ρ x₀ ℓ r h k c w N θ ja t τ B H kernel ζ u
      (fun η => hmoment ζ η u) p hp)

theorem paperPhysicalPropensityPolynomial_retained {I J : Type*} [Fintype I]
    [Fintype J] [DecidableEq J] (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (x₀ : d → ℝ)
    (r h : ℝ) (k : d → ℤ) (c w N ja t τ : ℝ)
    (W : Representative.Array d (Fin Q) J 1) (u : Fin Q × d → ℝ) (z : Fin Q → ℝ) (ζ : J → Bool)
    (keep : I → Fin Q) (sites : I → d → ℝ) (hkeep : ∀ i, configurationSite u (keep i) = sites i)
    (R T siteJa rough offset ψ : I → ℝ) :
    paperPhysicalPropensityPolynomial Q ρ x₀ r h k c w N ja t τ W u z ζ
      (retainedPropensityPolynomial Q R T siteJa rough offset ψ sites) =
      (Fintype.card (Equiv.Perm (Fin Q)) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin Q),
        graphTaper edgeLeft edgeRight taperCutoff τ
          (graphDistance edgeLeft edgeRight (fun p => u (σ p.1, p.2))) *
          ((paperCoefficientLaw Q).expect (fun ω => propensityPolynomialFunctional
            (physicalPropensitySlotCorrection x₀ r h k c w N ja (fun p => u (σ p.1, p.2)))
            W (fun p => u (σ p.1, p.2)) (fun i => z (σ i)) ζ
            (∏ i, (C (increment (R i) (T i) (siteJa i) (ψ i * (t * N)) (rough i)) * X (σ.symm (keep i)) +
              C (likelihood (R i) (T i) (siteJa i)
                (offset i + ψ i * coefficientEvaluation (paperCoefficientAtoms Q ρ ω) (sites i)) (rough i))))) -
            (paperCoefficientLaw Q).expect (fun ω => ∏ i, likelihood (R i) (T i) (siteJa i)
              (offset i + ψ i * coefficientEvaluation (paperCoefficientAtoms Q ρ ω) (sites i)) (rough i)) *
                pointValue (torusProjection (fun p => u (σ p.1, p.2))) (fun i => z (σ i)) ζ W) := by
  simp only [paperPhysicalPropensityPolynomial, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  apply congrArg (fun x : ℝ => (Fintype.card (Equiv.Perm (Fin Q)) : ℝ)⁻¹ * x)
  apply Finset.sum_congr rfl
  intro σ _
  apply propensityCoefficientFunctional_retained Q hQ (by simp) (paperCoefficientLaw Q)
    (paperCoefficientAtoms Q ρ) (fun p => u (σ p.1, p.2)) τ (t * N) (fun i => σ.symm (keep i)) sites
  intro i
  change (fun j => u (σ (σ.symm (keep i)), j)) = sites i
  rw [Equiv.apply_symm_apply]
  exact hkeep i

end CausalLowerbound.PartC
