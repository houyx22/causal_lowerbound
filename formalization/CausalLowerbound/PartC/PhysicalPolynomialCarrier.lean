import CausalLowerbound.PartC.PolynomialCarrier
import CausalLowerbound.PartC.PairedPhysicalDensity
import CausalLowerbound.PartC.CarrierSymbolBound

/-! The polynomial carrier realized by actual normalized physical densities.
For a bounded symmetric target, all polarization and probability objects
are constructed, and the fixed point retains the one-symbol volume gain.
The mixed-case target operator itself is still a separate construction. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Representative

variable {d ι I Γ : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]
  [Nonempty ι] [Fintype I] [Fintype Γ] {D : ℕ}

set_option maxHeartbeats 600000 in
theorem exists_physical_polynomial_carrier (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ y : d → ℝ, 0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 < θ) (hθ1 : θ < 1)
    (T : Array d ι (activeBlocks (d := d) ℓ h) D →L[ℝ]
      (I → Array d ι (activeBlocks (d := d) ℓ h) D))
    (δ : ℝ) (hδ : 0 ≤ δ) (hT : ∀ a, ‖T a‖ ≤ δ * ‖a‖)
    (hsym : ∀ a i x z ζ (σ : Equiv.Perm ι),
      pointValue (Wiener.permuteSlots σ x) (fun j => z (σ j)) ζ (T a i) = pointValue x z ζ (T a i))
    (feature : I → Γ → ℝ) (μ : FiniteLaw Γ) (hμ : ∀ y, 0 < μ.weight y) (radius : ℝ)
    (realize : ∀ v : I → ℝ, (∀ i, |v i| ≤ radius) →
      ∃ ν : FiniteLaw Γ, (∀ y, 0 < ν.weight y) ∧
        ∀ i, ν.expect (feature i) = μ.expect (feature i) + v i)
    (K : ℝ) (hK : 0 < K) (hinv : K⁻¹ ≤ radius)
    (hsmall : K * ((1 + |θ|) ^ Fintype.card ι + 1) *
      (2 * (((Fintype.card I : ℝ) * polarizationBound ι θ) * δ)) ≤ 1 / 2)
    (hmass : 2 * K * (2 * (((Fintype.card I : ℝ) * polarizationBound ι θ) * δ)) < 1) :
    let L := ((Fintype.card I : ℝ) * polarizationBound ι θ) * δ
    ∃ (B : Array d ι (activeBlocks (d := d) ℓ h) D) (H : DiscreteLaw ℕ)
        (kernel : (activeBlocks (d := d) ℓ h → Bool) → ℕ → FiniteLaw Γ),
      reflection B = B ∧ ‖B‖ ≤ 2 ∧
      ‖B - unit‖ ≤ 2 * (K * ((1 + |θ|) ^ Fintype.card ι + 1) * (L + L)) ∧
      (∀ j : activeBlocks (d := d) ℓ h, ‖symbolPart j B‖ ≤ 2 * K * (L + L) *
        ((Fintype.card ι : ℝ) * ((θ / 2) * ((D / N₀) * (ℓ / (2 * r)) ^ Fintype.card d)) *
          (1 + θ) ^ (Fintype.card ι - 1))) ∧
      0 < H.weight 0 ∧
      (∀ n, H.weight (PairedSeries.flipLabel n + 1) = H.weight (n + 1)) ∧
      (∀ ζ, kernel ζ 0 = μ) ∧ (∀ ζ n y, 0 < (kernel ζ n).weight y) ∧
      (∀ ζ n, (∑ y, (H.joint (kernel ζ)).weight (n, y)) = H.weight n) ∧
      HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom unit
        (pairedAtom reflection (naturalPhysicalAtom (ι := ι) (D := D) x₀ ℓ r h k c w N θ)) n) B ∧
      (∀ ζ (u : UnitChart (ι × d)), HasSum (fun n => H.weight n *
        ∏ j, carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ (fun q => u.val (j, q)))
        (pointValue (Wiener.torusProjection u.val)
          (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun q => u.val (j, q))) ζ B)) ∧
      ∀ ζ i (u : UnitChart (ι × d)), HasSum (fun n => (H.weight n *
        ((kernel ζ n).expect (feature i) - μ.expect (feature i))) *
        ∏ j, carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ (fun q => u.val (j, q)))
        (pointValue (Wiener.torusProjection u.val)
          (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun q => u.val (j, q))) ζ (T B i)) := by
  let center := physicalPolynomialCenters (ι := ι) (D := D) x₀ ℓ r h k c w N
  have hcenter : ∀ v i, ‖center v i‖ ≤ 1 := fun v i =>
    (normalizedTrigCenter_bounds x₀ ℓ r h k c w N N₀ hℓ hr hc hN₀ hN hm hrough
      (v i).1.val (v i).2.1 (v i).2.2).1
  let chart : UnitChart (ι × d) → Wiener.Torus (ι × d) := fun u => Wiener.torusProjection u.val
  have hchart : Continuous chart := Wiener.torusProjection_quotient.continuous.comp continuous_subtype_val
  let z (ζ : activeBlocks (d := d) ℓ h → Bool) (i : ι) (u : UnitChart (ι × d)) :=
    normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u.val (i, j))
  have hz (ζ : activeBlocks (d := d) ℓ h → Bool) (i : ι) : Continuous (z ζ i) :=
    (normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ).comp
      (continuous_pi (fun j => (continuous_apply (i, j)).comp continuous_subtype_val))
  have hb (ζ : activeBlocks (d := d) ℓ h → Bool) (i : ι) (u : UnitChart (ι × d)) : |z ζ i u| ≤ 1 :=
    normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ _
  have hflip (ζ : activeBlocks (d := d) ℓ h → Bool) (i : ι) (u : UnitChart (ι × d)) :
      z (Walsh.flip ζ) i u = -z ζ i u := normalizedRoughChart_flip x₀ ℓ r h k c w N ζ _
  obtain ⟨B, H, kernel, hfixed, hreflect, hball, hzeroMass, hweight, hpaired,
      hzero, hpositive, hmarginal, hdensity, heval, hmoment⟩ :=
    exists_polynomial_sign_carrier center hcenter θ hθ.ne' T δ hδ hT
      chart hchart z hz hb hflip
      (fun a ζ i u σ => hsym a i (chart u) (fun j => z ζ j u) ζ σ.symm)
      feature μ hμ radius realize K hK hinv hsmall hmass
  let L := ((Fintype.card I : ℝ) * polarizationBound ι θ) * δ
  let M := (1 + |θ|) ^ Fintype.card ι + 1
  let C := polynomialCarrierCoefficients center hcenter θ T δ hT
  let atom := pairedAtom reflection (naturalPhysicalAtom (ι := ι) (D := D) x₀ ℓ r h k c w N θ)
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (polarizationBound_nonneg θ)) hδ
  have hsmall' : K * M * (L + L) ≤ 1 / 2 := by simpa only [M, L, two_mul] using hsmall
  have hB : ‖B‖ ≤ 2 := by
    have hb1 : ‖B - unit‖ ≤ 1 := hball.trans (by linarith [hsmall'])
    calc
      ‖B‖ ≤ ‖B - unit‖ + ‖(unit : Array d ι (activeBlocks (d := d) ℓ h) D)‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (B - (unit : Array d ι (activeBlocks (d := d) ℓ h) D)) unit
      _ ≤ 2 := by rw [unit_norm]; linarith
  have hatom : ∀ n, ‖atom n - unit‖ ≤ M :=
    pairedAtom_bound reflection (fun a => (reflection_norm a).le) unit reflection_unit
      (naturalPhysicalAtom (ι := ι) (D := D) x₀ ℓ r h k c w N θ) M
      (naturalPolynomialAtom_sub_unit_bound center hcenter θ)
  refine ⟨B, H, kernel, hreflect, hB, hball, ?_, hzeroMass, hpaired,
    hzero, hpositive, hmarginal, hdensity, ?_, ?_⟩
  · intro j
    exact carrier_symbol_bound_of_norm C K hK.le (add_nonneg hL hL) unit B atom M hatom hfixed hB
      (symbolPart j) (symbolPart_unit j) _ (by positivity)
      (fun n => pairedPhysicalAtom_symbol_bound x₀ ℓ r h k c w N N₀ θ
        hℓ hr hc hN₀ hN hm hrough hθ.le hθ1 n j)
  · intro ζ u
    have hs := (ContinuousMap.evalCLM ℝ u).hasSum (heval ζ)
    have he (n : ℕ) : pointValue (chart u) (fun j => z ζ j u) ζ
        (CarrierCoefficients.labeledAtom unit (pairedAtom reflection (naturalPolynomialAtom center θ)) n) =
          ∏ j, carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ (fun q => u.val (j, q)) :=
      carrierPhysicalAtom_value x₀ ℓ r h k c w N θ n ζ u.val
    simpa only [map_smul, ContinuousMap.evalCLM_apply, chartEvaluation_apply, chart, z,
      he, smul_eq_mul] using hs
  · intro ζ i u
    have hs := (ContinuousMap.evalCLM ℝ u).hasSum (hmoment ζ i)
    have he (n : ℕ) :
        ContinuousMap.evalCLM ℝ u (CarrierCoefficients.labeledAtom
          (chartEvaluation (D := D) chart hchart (z ζ) (hz ζ) (hb ζ) ζ unit)
          (fun m => chartEvaluation chart hchart (z ζ) (hz ζ) (hb ζ) ζ
            (pairedAtom reflection (naturalPolynomialAtom center θ) m)) n) =
          ∏ j, carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ (fun q => u.val (j, q)) := by
      cases n with
      | zero => simp only [CarrierCoefficients.labeledAtom, ContinuousMap.evalCLM_apply,
          chartEvaluation_apply, pointValue_unit, carrierPhysicalDensity, Finset.prod_const_one]
      | succ m => exact pairedPhysicalAtom_value x₀ ℓ r h k c w N θ m ζ u.val
    simpa only [map_smul, he, smul_eq_mul, ContinuousMap.evalCLM_apply, chartEvaluation_apply, chart, z] using hs

end CausalLowerbound.PartC
