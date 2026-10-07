import CausalLowerbound.PartC.PhysicalOutcomeTarget
import CausalLowerbound.PartC.PhysicalPolynomialCarrier

/-! The actual positive degree-three carrier on the complete coefficient
grid. The variance, symmetric target, and moment realization are all
constructed; only explicit norm smallness remains for the scale theorem. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def outcomeTargetBound (Q : ℕ) (C N t τ : ℝ) : ℝ :=
  C * ((levelBudget 2 τ + 1 : ℕ) : ℝ) ^ Q.choose 2 *
    ∑ j ∈ Finset.Icc 1 (4 * Q), ((t * N) / τ) ^ j

def HasPaperOutcomeCarrier (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ t τ K δ : ℝ) : Prop :=
  (∀ n ζ, Continuous (carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ)) ∧
  (∀ n ζ, (∫ u in Set.Icc (0 : d → ℝ) 1,
    carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ u) = 1) ∧
  (∀ n ζ u, 1 - θ ≤ carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ u ∧
    carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ u ≤ 1 + θ) ∧
  let I := MomentExponent (CoefficientExponent d Q) (4 * Q)
  let L := ((Fintype.card I : ℝ) * polarizationBound (Fin Q) θ) * δ
  ∃ (B : Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (H : DiscreteLaw ℕ)
      (kernel : (activeBlocks (d := d) ℓ h → Bool) → ℕ →
        FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
    reflection B = B ∧ ‖B‖ ≤ 2 ∧
    ‖B - unit‖ ≤ 2 * (K * ((1 + |θ|) ^ Q + 1) * (L + L)) ∧
    (∀ j : activeBlocks (d := d) ℓ h, ‖symbolPart j B‖ ≤ 2 * K * (L + L) *
      ((Q : ℝ) * ((θ / 2) * ((3 / N₀) * (ℓ / (2 * r)) ^ Fintype.card d)) * (1 + θ) ^ (Q - 1))) ∧
    0 < H.weight 0 ∧
    (∀ n, H.weight (PairedSeries.flipLabel n + 1) = H.weight (n + 1)) ∧
    (∀ ζ, kernel ζ 0 = paperCoefficientLaw Q) ∧ (∀ ζ n y, 0 < (kernel ζ n).weight y) ∧
    (∀ ζ n, (∑ y, (H.joint (kernel ζ)).weight (n, y)) = H.weight n) ∧
    HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom unit
      (pairedAtom reflection (naturalPhysicalAtom (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ)) n) B ∧
    (∀ ζ (u : UnitChart (Fin Q × d)), HasSum (fun n => H.weight n *
      ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ (fun a => u.val (j, a)))
      (pointValue (torusProjection u.val)
        (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u.val (j, a))) ζ B)) ∧
    ∀ ζ i (u : UnitChart (Fin Q × d)), HasSum (fun n => (H.weight n *
      ((kernel ζ n).expect (monomialFeature (paperCoefficientAtoms Q ρ) i) -
        (paperCoefficientLaw Q).expect (monomialFeature (paperCoefficientAtoms Q ρ) i))) *
      ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ (fun a => u.val (j, a)))
      (paperPhysicalOutcomeValue Q ρ x₀ r h k c w N t τ B i u.val
        (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u.val (j, a))) ζ)

set_option maxHeartbeats 800000 in
theorem exists_paperOutcomeCarrier (Q : ℕ) [NeZero Q] (ρ θ : ℝ) (hρ : 0 < ρ)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C ≥ 0, ∃ K > 0, ∀ (x₀ : d → ℝ) (ℓ r h : ℝ), 0 < ℓ → 0 < r → r ≤ h →
      ∀ (k : activeBlocks (d := d) r h) (c w N N₀ t τ : ℝ),
      0 < c → 0 < w → w ≤ 1 / 2 → 0 < N₀ → N₀ / c ≤ N → 0 < t → 0 < τ →
      (∀ y : d → ℝ, 0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c) →
      (∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) →
      ∀ M : Fourier d, ‖M‖ ≤ N →
      (∀ u ∈ Set.Icc (0 : d → ℝ) 1, toContinuous M (torusProjection u) =
        (assignmentMultiplier c w (fun j => 4 * u j - 2) : ℂ)) →
      let δ := outcomeTargetBound Q C N t τ
      let P := (Fintype.card (MomentExponent (CoefficientExponent d Q) (4 * Q)) : ℝ) * polarizationBound (Fin Q) θ
      K * ((1 + |θ|) ^ Q + 1) * (2 * (P * δ)) ≤ 1 / 2 →
      2 * K * (2 * (P * δ)) < 1 →
      HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ t τ K δ := by
  obtain ⟨C, hC, htarg⟩ := exists_physical_paperOutcomeTarget (d := d) Q ρ
  obtain ⟨radius, hradius, realize⟩ := paper_outcome_moment_radius (d := d) Q ρ hρ
  let K := radius⁻¹
  have hK : 0 < K := inv_pos.mpr hradius
  refine ⟨C, hC, K, hK, fun x₀ ℓ r h hℓ hr hrh k c w N N₀ t τ
    hc hw hw1 hN₀ hN ht hτ hm hrough M hM hMv => ?_⟩
  dsimp only
  intro hsmall hmass
  have hNp : 0 < N := (div_pos hN₀ hc).trans_le hN
  obtain ⟨T, hT, hsym, _, hvalue⟩ := htarg (activeBlocks (d := d) ℓ h)
    x₀ r h hr hrh k c w N t τ hw hw1 hNp ht hτ M hM hMv
  have hδ : 0 ≤ outcomeTargetBound Q C N t τ := by
    unfold outcomeTargetBound
    apply mul_nonneg (mul_nonneg hC (by positivity))
    exact Finset.sum_nonneg (fun j _ => pow_nonneg (by positivity) j)
  obtain ⟨B, H, kernel, hreflect, hnorm, hball, hsymbol, hzero, hpaired, hbase, hpositive,
      hmarginal, hseries, hdensity, hmoment⟩ :=
    exists_physical_polynomial_carrier (ι := Fin Q) (D := 3) x₀ ℓ r h k.val c w N N₀ θ
      hℓ hr hc hN₀ hN hm hrough hθ hθ1 T (outcomeTargetBound Q C N t τ) hδ hT hsym
      (monomialFeature (paperCoefficientAtoms Q ρ)) (paperCoefficientLaw Q) (gridLaw_weight_pos (4 * Q))
      radius realize K hK (by simp [K])
      (by simpa only [Fintype.card_fin] using hsmall) hmass
  refine ⟨carrierPhysicalDensity_continuous x₀ ℓ r h k.val c w N θ hc,
    carrierPhysicalDensity_integral x₀ ℓ r h k.val c w N θ hc,
    carrierPhysicalDensity_range x₀ ℓ r h k.val c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ.le,
    B, H, kernel, hreflect, hnorm, ?_, ?_, hzero, hpaired, hbase, hpositive,
    hmarginal, hseries, hdensity, ?_⟩
  · simpa only [Fintype.card_fin] using hball
  · simpa only [Fintype.card_fin, Nat.cast_ofNat] using hsymbol
  · intro ζ i u
    have hmom := hmoment ζ i u
    rw [hvalue B i u.val u.property
      (fun j => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (fun a => u.val (j, a))) ζ] at hmom
    exact hmom

end CausalLowerbound.PartC
