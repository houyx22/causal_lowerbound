import CausalLowerbound.PartB.IdealIncrementVector

/-! The full vector Ψ_{4Q}, formed from every nonconstant coordinate
monomial of degree at most 4Q. This instantiates the concrete Wiener estimate
and the positive polarization/carrier theorem for the complete Q-site graph.
The finite support and its moment right inverse are model-construction inputs. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped BigOperators Topology

namespace CausalLowerbound.PartB.ShellGeometry
open Wiener

-- Keep the Fin specializations aligned with the ordered-graph interface.
local instance finOrderedDecEq (Q : ℕ) : DecidableEq (Fin Q) :=
  fun a b => LinearOrder.toDecidableEq a b
local instance finOrderedDecLt (Q : ℕ) : DecidableRel ((· < ·) : Fin Q → Fin Q → Prop) :=
  fun a b => LinearOrder.toDecidableLT a b

variable {A Ω d : Type*} [Fintype A] [DecidableEq A] [Fintype Ω] [Fintype d] [DecidableEq d]

/-- The canonical, repetition-free index set of nonconstant monomials. -/
abbrev MomentExponent (A : Type*) [Fintype A] (D : ℕ) :=
  {η : A → Fin (D + 1) // 0 < ∑ a, (η a).val ∧ (∑ a, (η a).val) ≤ D}

abbrev MomentPositions {D : ℕ} (η : MomentExponent A D) := (a : A) × Fin (η.val a).val

def monomialFeature {D : ℕ} (U : Ω → A → ℝ) (η : MomentExponent A D) (ω : Ω) : ℝ :=
  ∏ a, U ω a ^ (η.val a).val

theorem momentPositions_card {D : ℕ} (η : MomentExponent A D) :
    Fintype.card (MomentPositions η) ≤ D := by
  simpa only [MomentPositions, Fintype.card_sigma, Fintype.card_fin] using η.property.2

theorem monomialFeature_word {D : ℕ} (U : Ω → A → ℝ) (η : MomentExponent A D) (ω : Ω) :
    (∏ k : MomentPositions η, U ω k.1) = monomialFeature U η ω := by
  simp [MomentPositions, monomialFeature, Fintype.prod_sigma]

/-- All coordinates of the tapered ideal increment for Ψ_{4Q}. A specifies
the finite coefficient basis, and basis gives its actual polynomial degrees. -/
def partBIdealVector (Q : ℕ) (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (basis : A → d × Bool →₀ ℕ) (p B : ℝ) (n : ℕ) : MomentExponent A (4 * Q) → SymmetricReal d (Fin Q) :=
  idealMomentVector μ (fun η ω (k : MomentPositions η) => U ω k.1)
    (fun η (k : MomentPositions η) => basis k.1) p B n

theorem partBIdealVector_value (Q : ℕ) (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (basis : A → d × Bool →₀ ℕ) (p B : ℝ) (n : ℕ) (η : MomentExponent A (4 * Q))
    (u : Fin Q × d → ℝ) :
    toContinuous (partBIdealVector Q μ U basis p B n η) (torusProjection u) =
      ((ConfigurationShells.graphTaper edgeLeft edgeRight taperCutoff
        (logarithmicThreshold p B (n + 1)) (graphDistance edgeLeft edgeRight u) *
        ((μ.prod (independentSigns (ι := Fin Q))).expect (fun z =>
          ∏ a, (U z.1 a + polynomialAmplitude p (n + 1) *
            ∑ i : Fin Q, lagrangeCoefficient edgeLeft edgeRight i (basis a) u * sign (z.2 i)) ^ (η.val a).val)
          - μ.expect (monomialFeature U η))) : ℝ) := by
  rw [show monomialFeature U η = (fun ω => ∏ a, U ω a ^ (η.val a).val) by rfl]
  rw [show partBIdealVector Q μ U basis p B n η =
    symmetricIdealSequence μ (fun ω (k : MomentPositions η) => U ω k.1)
      (fun k : MomentPositions η => basis k.1) p B n by rfl,
    symmetricIdealSequence_value]
  unfold idealIncrement idealMonomialMoment
  simp only [monomialFeature_word, monomialFeature, MomentPositions, Fintype.prod_sigma, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The exact inverse-square estimate for every coordinate of Ψ_{4Q},
with the paper's exponent E_Q = choose Q 2. -/
theorem partB_wiener_strong (Q : ℕ) (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (basis : A → d × Bool →₀ ℕ) :
    ∃ C ≥ 0, ∀ p B (n : ℕ), logarithmicThreshold p B (n + 1) ≤ 1 →
      ‖partBIdealVector Q μ U basis p B n‖ ≤
        C * (1 + Real.log (1 / logarithmicThreshold p B (n + 1))) ^ Q.choose 2 *
          ∑ j ∈ Finset.Icc 2 (4 * Q),
            (polynomialAmplitude p (n + 1) / logarithmicThreshold p B (n + 1)) ^ j := by
  simpa only [partBIdealVector, completeEdge_card] using
    idealMomentVector_log_bound (V := Fin Q) μ
      (fun η ω (k : MomentPositions η) => U ω k.1)
      (fun η (k : MomentPositions η) => basis k.1) (4 * Q) momentPositions_card

theorem partB_wiener_rate (Q : ℕ) (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (basis : A → d × Bool →₀ ℕ) (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖partBIdealVector Q μ U basis p B n‖ ≤ C * logScale (n + 1) ^ ((Q.choose 2 : ℝ) - 2 * B) := by
  simpa only [partBIdealVector, completeEdge_card] using
    idealMomentVector_rate (V := Fin Q) μ
      (fun η ω (k : MomentPositions η) => U ω k.1)
      (fun η (k : MomentPositions η) => basis k.1) p B hp hB

theorem partB_wiener_vanishes (Q : ℕ) (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (basis : A → d × Bool →₀ ℕ) (p B : ℝ) (hp : 0 < p)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    Tendsto (fun n => ‖partBIdealVector Q μ U basis p B n‖) atTop (𝓝 0) := by
  have hb : (Fintype.card (CompleteEdge (Fin Q)) : ℝ) < 2 * B := by
    rw [completeEdge_card]; linarith
  simpa only [partBIdealVector] using idealMomentVector_norm_tendsto (V := Fin Q) μ
    (fun η ω (k : MomentPositions η) => U ω k.1)
    (fun η (k : MomentPositions η) => basis k.1) p B hp hb

/-- Item 1: the concrete ideal increment, its vanishing Wiener norm, and
the explicit positive polarization are assembled. The finite moment right
inverse is the separate support-construction obligation (item 2). -/
theorem partB_analytic_positiveCarrier (Q : ℕ) [NeZero Q]
    (μ : FiniteLaw Ω) (U : Ω → A → ℝ) (basis : A → d × Bool →₀ ℕ)
    (p B : ℝ) (hp : 0 < p) (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B)
    (hμ : ∀ ω, 0 < μ.weight ω) (R : MomentRightInverse (monomialFeature (D := 4 * Q) U)) :
    ∀ᶠ n in atTop, HasPositiveCarrier 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) (1 / 4))
      (multiplicationIncrement (partBIdealVector Q μ U basis p B n)) (monomialFeature U) μ := by
  exact PositiveWiener.eventually_hasPositiveWienerCarrier
    (partBIdealVector Q μ U basis p B) (fun n => ‖partBIdealVector Q μ U basis p B n‖)
    (fun _ => norm_nonneg _) (partB_wiener_vanishes Q μ U basis p B hp hB)
    (fun _ => le_rfl) (monomialFeature U) μ hμ R

end CausalLowerbound.PartB.ShellGeometry
