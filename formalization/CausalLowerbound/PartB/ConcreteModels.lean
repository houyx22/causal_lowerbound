import CausalLowerbound.PartB.SmallDensityCarrier
import CausalLowerbound.PartB.DesignExperiments
import CausalLowerbound.PartB.BalancedScales
import CausalLowerbound.PartB.CarrierLocalization

/-! Item 2: the explicit small-support model and both complete parameter
rows are legal for prescribed radii and density bounds. The carrier used
here has the very same arbitrarily small density contrast. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Topology
open MeasureTheory Filter
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def DesignLegal (lower upper : ℝ) (f : (d → ℝ) → ℝ) : Prop :=
  Measurable f ∧ (∫ x, f x ∂cubeMeasure d) = 1 ∧ ∀ x, lower ≤ f x ∧ f x ≤ upper

def ModelLegal (α β γ : Regularity) (Lπ L₀ Lτ κ lower upper : ℝ)
    (fields : NuisanceFields d) (f : (d → ℝ) → ℝ) : Prop :=
  fields.Legal α β γ Lπ L₀ Lτ κ ∧ DesignLegal lower upper f

/-- No inverse, Wiener bound, interpolation bound, Hölder bound, or design
normalization is supplied as an assumption. Those inputs are constructed. -/
theorem paper_item_two (Q : ℕ) [NeZero Q] (ρ : ℝ) (hρ : 0 < ρ)
    (α β γ : Regularity) (hβγ : β.exponent ≤ γ.exponent)
    (Lπ L₀ Lτ κ lower upper : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ)
    (hκ : κ < 1 / 4) (hl : lower < 1) (hu : 1 < upper)
    (p B : ℝ) (hp : 0 < p) (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    ∃ θ ε : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < ε ∧ ε ≤ 1 ∧
      (∀ᶠ n in atTop,
        HasPositiveCarrier 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) θ)
          (multiplicationIncrement
            (paperIdealVector Q (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ) p B n))
          (monomialFeature (paperCoefficientAtoms Q ρ)) (paperCoefficientLaw Q)) ∧
      (∀ (ca cb : ℝ), 0 ≤ ca → ca ≤ ε → 0 ≤ cb → cb ≤ ε →
        ∀ (side : Bool) (S : Finset (d → ℤ))
          (sample : (d → ℤ) → MomentGrid (CoefficientExponent d Q) (4 * Q))
          (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r h t : ℝ),
          0 < r → r ≤ h → h ≤ 1 → 0 ≤ t → t ≤ 1 →
          h ^ γ.exponent = r ^ (α.exponent + β.exponent) * t ^ 2 →
          ModelLegal α β γ Lπ L₀ Lτ κ lower upper
            (modelFields side S (fun k => paperCoefficientAtoms Q ρ (sample k)) x₀ r h
              (ca * r ^ α.exponent) (cb * r ^ β.exponent) t (ca * cb * h ^ γ.exponent))
            (normalizedDesign Q S θ H x₀ r)) := by
  obtain ⟨θ, hθ, hθ1, hθlo, hθhi⟩ := exists_design_contrast (5 ^ Fintype.card d) lower upper hl hu
  obtain ⟨ε, hε, hε1, hmodel⟩ := exists_legal_amplitudes (paperCoefficientAtoms (d := d) Q ρ)
    α β γ hβγ Lπ L₀ Lτ κ hLπ hL₀ hLτ hκ
  refine ⟨θ, ε, hθ, hθ1, hε, hε1,
    paper_positiveCarrier_contrast Q ρ θ hρ hθ p B hp hB, ?_⟩
  intro ca cb hca hcaε hcb hcbε side S sample H x₀ r h t hr hrh hh1 ht ht1 hbal
  have hf := normalizedDesign_legal Q S θ hθ.le hθ1 H x₀ r
  exact ⟨hmodel ca cb hca hcaε hcb hcbε side S sample x₀ r h t hr hrh hh1 ht ht1 hbal,
    hf.1, hf.2.1, fun x => ⟨hθlo.trans (hf.2.2 x).1, (hf.2.2 x).2.trans hθhi⟩⟩

/-- Positive fixed amplitudes and an actual polynomial sequence of models.
The scale inequalities are explicit; selecting the optimal rate exponents
and proving the global information bound belongs to item 3. -/
theorem paper_item_two_polynomial (Q : ℕ) [NeZero Q] (ρ : ℝ) (hρ : 0 < ρ)
    (α β γ : Regularity) (hβγ : β.exponent ≤ γ.exponent) (hγ : 0 < γ.exponent)
    (Lπ L₀ Lτ κ lower upper : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ)
    (hκ : κ < 1 / 4) (hl : lower < 1) (hu : 1 < upper)
    (z ξ B : ℝ) (hz : 0 ≤ z) (hξ : z / γ.exponent ≤ ξ)
    (hp : ξ * (α.exponent + β.exponent) < z)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    let p := (z - ξ * (α.exponent + β.exponent)) / 2
    ∃ θ ca cb : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < ca ∧ 0 < cb ∧
      ∀ᶠ n : ℕ in atTop,
        HasPositiveCarrier 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) θ)
          (multiplicationIncrement
            (paperIdealVector Q (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ) p B n))
          (monomialFeature (paperCoefficientAtoms Q ρ)) (paperCoefficientLaw Q) ∧
        ∀ (side : Bool) (S : Finset (d → ℤ))
          (sample : (d → ℤ) → MomentGrid (CoefficientExponent d Q) (4 * Q))
          (H : (d → ℤ) → ℕ) (x₀ : d → ℝ),
          let r := ((n + 1 : ℕ) : ℝ) ^ (-ξ)
          let h := ((n + 1 : ℕ) : ℝ) ^ (-(z / γ.exponent))
          let t := polynomialAmplitude p (((n + 1 : ℕ) : ℝ))
          ModelLegal α β γ Lπ L₀ Lτ κ lower upper
            (modelFields side S (fun k => paperCoefficientAtoms Q ρ (sample k)) x₀ r h
              (ca * r ^ α.exponent) (cb * r ^ β.exponent) t (ca * cb * h ^ γ.exponent))
            (normalizedDesign Q S θ H x₀ r) := by
  let p := (z - ξ * (α.exponent + β.exponent)) / 2
  have hp0 : 0 < p := by dsimp [p]; linarith
  obtain ⟨θ, ε, hθ, hθ1, hε, hε1, hcarrier, hmodel⟩ :=
    paper_item_two (d := d) Q ρ hρ α β γ hβγ Lπ L₀ Lτ κ lower upper hLπ hL₀ hLτ hκ hl hu
      p B hp0 hB
  refine ⟨θ, ε / 2, ε / 2, hθ, hθ1, by positivity, by positivity, ?_⟩
  filter_upwards [hcarrier] with n hn
  refine ⟨hn, ?_⟩
  intro side S sample H x₀
  have hx : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hsc := polynomial_scales_balanced α.exponent β.exponent γ.exponent z ξ
    ((n + 1 : ℕ) : ℝ) hx hγ hz hξ hp0.le
  exact hmodel (ε / 2) (ε / 2) (by positivity) (by linarith) (by positivity) (by linarith)
    side S sample H x₀ _ _ _ hsc.1 hsc.2.1 hsc.2.2.1 hsc.2.2.2.1 hsc.2.2.2.2.1 hsc.2.2.2.2.2

end CausalLowerbound.PartB.ShellGeometry
