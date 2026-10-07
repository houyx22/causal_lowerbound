import CausalLowerbound.PartC.PhysicalPropensityComparison
import CausalLowerbound.PartC.RawPropensityExpansion

/-! Average the actual pattern comparison over the paper coefficient law.
The explicit error is independent of the coefficient draw and can later
be averaged over the finite slot permutations as well. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {Ω Γ d I : Type*} [Fintype Ω] [Fintype Γ]
  [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem double_average_comparison_bound (μ : FiniteLaw Ω) (ν : FiniteLaw Γ)
    (f g : Ω → Γ → ℝ) (C : Γ → ℝ)
    (h : ∀ γ, |μ.expect (fun ω => f ω γ) - μ.expect (fun ω => g ω γ)| ≤ C γ) :
    |μ.expect (fun ω => ν.expect (f ω)) - μ.expect (fun ω => ν.expect (g ω))| ≤ ν.expect C := by
  rw [FiniteLaw.expect_comm μ ν f, FiniteLaw.expect_comm μ ν g, ← FiniteLaw.expect_sub]
  exact (ν.abs_expect_le _).trans (ν.expect_mono h)

def propensityComparisonError
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ ja b t τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) : ℝ :=
  let T := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
  let C := 1 + N₀ / c + 1 / (c * N₀)
  let signCost := (2 * C ^ Q) ^ Fintype.card S * ∑ k, ∑ j ∈ T,
    C ^ Q * (2 * ‖symbolPart j (B k)‖ + ‖B k - unit‖ *
      ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
  let taperCost := (2 * C ^ Q) ^ Fintype.card S * ∑ k,
    (2 * C ^ Q) * completedGhostTaperDefect Q (e k) τ
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
  let scale := (2 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) + 1) * (t * (ja * (1 + N₀)))
  (((Fintype.card S : ℝ) + 1) ^ Fintype.card I * b) *
    (signCost * scale + taperCost * scale) +
    signCost * ((2 : ℝ) ^ Fintype.card I * Fintype.card I * (|ja * b * t| / 2))

theorem physical_propensity_pattern_average_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ ja b t τ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hmb : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 0 ≤ t) (hbtja : b * t ≤ ja)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (G : S → Type) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (hsmooth : ∀ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    let base := propensityObservationUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N ja B x G e (fun _ => none)
    |independentSigns.expect (fun ζ => propensityObservationPatternSum Q hQ ρ false S x₀ ℓ r h c w N ja b t τ B ζ x y G e) -
      independentSigns.expect (fun ζ => (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)).expect (fun ξ =>
        base ζ ζ * ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
          (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i))))| ≤
      propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e := by
  dsimp only
  let base := propensityObservationUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N ja B x G e (fun _ => none)
  let f := fun ζ ξ => ∑ s : I → Option S,
    propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
      propensityObservationGhostProduct Q hQ S x₀ ℓ r h c w N ja τ B x G e s ζ ζ
  let g := fun ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) =>
    base ζ ζ * ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i))
  have he ξ : |independentSigns.expect (fun ζ => f ζ ξ) - independentSigns.expect (fun ζ => g ζ ξ)| ≤
      propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e :=
    physical_propensity_pattern_comparison_bound Q hQ ρ S x₀ ℓ r h c w N N₀ ja b t τ
      hℓ hr hh hw hw1 hc hN₀ hN hm hmb hrough hja hsmall hb hb1 ht hbtja
      B hB hreflect x y hsep hcover htr G e ξ (hsmooth ξ)
  have hd := double_average_comparison_bound independentSigns
    (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)) f g
    (fun _ => propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e) he
  simpa only [FiniteLaw.expect_const, f, g, base, propensityObservationPatternSum,
    propensityObservationGhostProduct] using hd

end CausalLowerbound.PartC
