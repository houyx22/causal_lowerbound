import CausalLowerbound.PartC.PhysicalFullMomentFunctional
import CausalLowerbound.PartC.CompletedMomentIntegrability
import CausalLowerbound.PartC.LocalPaperPropensityCarrier

/-! Retain one constructed carrier, law, and local coefficient kernel
together with their full polynomial moment identities. The witness is
constructed from the paper carrier theorem; integrability and projection
are derived from its actual density series, not supplied as assumptions. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

structure PropensityMomentWitness (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N θ ja t τ : ℝ) where
  representative : Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1
  law : DiscreteLaw ℕ
  kernel : (activeBlocks (d := d) ℓ h → Bool) → ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))
  reflection_fixed : reflection representative = representative
  norm_le : ‖representative‖ ≤ 2
  mass_zero_pos : 0 < law.weight 0
  paired_mass : ∀ n, law.weight (PairedSeries.flipLabel n + 1) = law.weight (n + 1)
  kernel_base : ∀ ζ, kernel ζ 0 = paperCoefficientLaw Q
  kernel_pos : ∀ ζ n y, 0 < (kernel ζ n).weight y
  atom_series : HasSum (fun n => law.weight n • CarrierCoefficients.labeledAtom unit
    (pairedAtom reflection (naturalPhysicalAtom (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ)) n) representative
  symbol_support : ∀ j ∉ carrierLocalSigns x₀ ℓ r h k, symbolPart j representative = 0
  kernel_local : ∀ ζ ζ', (∀ j ∈ carrierLocalSigns x₀ ℓ r h k, ζ j = ζ' j) → kernel ζ = kernel ζ'
  full_moment : ∀ ζ (u : UnitChart (Fin Q × d)) (p : MvPolynomial (CoefficientExponent d Q) ℝ),
    p.totalDegree ≤ 4 * Q → HasSum
      (fun n => (law.weight n * (kernel ζ n).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p)) *
        ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ (fun a => u.val (j, a)))
      (physicalPropensityFullFunctional Q ρ x₀ ℓ r h k c w N ja t τ representative ζ u.val p)

theorem exists_localPropensityMomentWitness
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0) (k : d → ℤ)
    (c w N N₀ θ ja t τ K δ : ℝ) (hc : 0 < c)
    (hcarr : HasPaperPropensityCarrier Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ) :
    let L := ((Fintype.card (MomentExponent (CoefficientExponent d Q) (4 * Q)) : ℝ) *
      polarizationBound (Fin Q) θ) * δ
    ∃ R : PropensityMomentWitness Q ρ x₀ ℓ r h k c w N θ ja t τ,
      ‖R.representative - unit‖ ≤ 2 * (K * ((1 + |θ|) ^ Q + 1) * (L + L)) ∧
      ∀ j : activeBlocks (d := d) ℓ h, ‖symbolPart j R.representative‖ ≤ 2 * K * (L + L) *
        ((Q : ℝ) * ((θ / 2) * ((1 / N₀) * (ℓ / (2 * r)) ^ Fintype.card d)) * (1 + θ) ^ (Q - 1)) := by
  obtain ⟨B, H, kernel, href, hnorm, hball, hsymbol, hzero, hpair, hbase, hpos,
    _, hseries, hdensity, hmoment, hsupport, hlocal⟩ :=
      hcarr.local_realization Q ρ x₀ ℓ r h hr k c w N N₀ θ ja t τ K δ hc
  refine ⟨{
    representative := B
    law := H
    kernel := kernel
    reflection_fixed := href
    norm_le := hnorm
    mass_zero_pos := hzero
    paired_mass := hpair
    kernel_base := hbase
    kernel_pos := hpos
    atom_series := hseries
    symbol_support := hsupport
    kernel_local := hlocal
    full_moment := ?_
  }, hball, hsymbol⟩
  intro ζ u p hp
  rw [physicalPropensityFullFunctional_apply]
  have hs := hasSum_weighted_expect (paperCoefficientLaw Q) (kernel ζ) H.weight _ _ _ _ (hdensity ζ u)
    (physical_propensity_polynomial_hasSum Q ρ x₀ ℓ r h k c w N θ ja t τ B H kernel ζ u
      (fun η => hmoment ζ η u) p hp)
  exact hs

namespace PropensityMomentWitness
variable {Q : ℕ} {ρ : ℝ} {x₀ : d → ℝ} {ℓ r h : ℝ} {k : d → ℤ} {c w N N₀ θ ja t τ K δ : ℝ}
variable (R : PropensityMomentWitness Q ρ x₀ ℓ r h k c w N θ ja t τ)
variable {I G : Type*} [Fintype I] [Fintype G]

theorem full_integrable
    (hcarr : HasPaperPropensityCarrier Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ) (hθ : 0 ≤ θ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1)
    (p : MvPolynomial (CoefficientExponent d Q) ℝ) (hp : p.totalDegree ≤ 4 * Q) :
    Integrable (fun z : G → d → ℝ => physicalPropensityFullFunctional Q ρ x₀ ℓ r h k c w N ja t τ
      R.representative ζ (completedConfiguration e u z) p) (Measure.pi (fun _ : G => cubeMeasure d)) := by
  let f := fun ω => eval (paperCoefficientAtoms Q ρ ω) p
  have hf (ω) : |f ω| ≤ ∑ y, |f y| :=
    Finset.single_le_sum (fun y _ => abs_nonneg (f y)) (Finset.mem_univ ω)
  exact completed_integrable_of_hasSum R.law
    (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
    (fun n => (R.kernel ζ n).expect f) (1 + θ) (∑ y, |f y|) (by linarith)
    (fun n => hcarr.1 n ζ) (fun n x => hcarr.density_abs_le n ζ x)
    (fun n => (R.kernel ζ n).abs_expect_le_bound f _ hf)
    (fun v => physicalPropensityFullFunctional Q ρ x₀ ℓ r h k c w N ja t τ R.representative ζ v p)
    (fun v => R.full_moment ζ v p hp) e u hu

theorem weighted_projective
    (hcarr : HasPaperPropensityCarrier Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ) (hθ : 0 ≤ θ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1)
    (p : MvPolynomial (CoefficientExponent d Q) ℝ) (hp : p.totalDegree ≤ 4 * Q) :
    weightedCarrierMarginal R.law
      (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
      (fun n => (R.kernel ζ n).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p)) u =
      ∫ z : G → d → ℝ, physicalPropensityFullFunctional Q ρ x₀ ℓ r h k c w N ja t τ
        R.representative ζ (completedConfiguration e u z) p ∂Measure.pi (fun _ : G => cubeMeasure d) := by
  let f := fun ω => eval (paperCoefficientAtoms Q ρ ω) p
  have hf (ω) : |f ω| ≤ ∑ y, |f y| :=
    Finset.single_le_sum (fun y _ => abs_nonneg (f y)) (Finset.mem_univ ω)
  exact hcarr.projective_hasSum hθ R.law ζ (fun n => (R.kernel ζ n).expect f) (∑ y, |f y|)
    (fun n => (R.kernel ζ n).abs_expect_le_bound f _ hf)
    (fun v => physicalPropensityFullFunctional Q ρ x₀ ℓ r h k c w N ja t τ R.representative ζ v p)
    (fun v => R.full_moment ζ v p hp) e u hu

end PropensityMomentWitness
end CausalLowerbound.PartC
