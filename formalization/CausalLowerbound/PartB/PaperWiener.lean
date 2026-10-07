import CausalLowerbound.PartB.PartBAnalyticComplete

/-! Specialization to the paper's complete polynomial coefficient space:
all monomials in the 2d embedding coordinates of total degree at most Q-1,
followed by all nonconstant coefficient moments of degree at most 4Q. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped BigOperators Topology

namespace CausalLowerbound.PartB.ShellGeometry
open Wiener

attribute [local instance] finOrderedDecEq finOrderedDecLt

variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

abbrev CoefficientExponent (d : Type*) [Fintype d] (Q : ℕ) :=
  {κ : d × Bool → Fin Q // (∑ a, (κ a).val) ≤ Q - 1}

def polynomialBasisDegree {Q : ℕ} (κ : CoefficientExponent d Q) : d × Bool →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun a => (κ.val a).val)

theorem polynomialBasisDegree_injective (Q : ℕ) :
    Function.Injective (polynomialBasisDegree (d := d) (Q := Q)) := by
  intro κ κ' h
  apply Subtype.ext
  funext a
  apply Fin.ext
  exact DFunLike.congr_fun h a

/-- No coefficient monomial of the prescribed degree is omitted. -/
theorem polynomialBasisDegree_complete (Q : ℕ) (hQ : 0 < Q) (κ : d × Bool →₀ ℕ)
    (hκ : (∑ a, κ a) ≤ Q - 1) :
    ∃ b : CoefficientExponent d Q, polynomialBasisDegree b = κ := by
  let b : d × Bool → Fin Q := fun a => ⟨κ a,
    lt_of_le_of_lt ((Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ a)).trans hκ)
      (Nat.sub_lt hQ (by decide))⟩
  refine ⟨⟨b, hκ⟩, ?_⟩
  apply Finsupp.ext
  intro a
  rfl

def paperIdealVector (Q : ℕ) (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (p B : ℝ) (n : ℕ) : MomentExponent (CoefficientExponent d Q) (4 * Q) → SymmetricReal d (Fin Q) :=
  partBIdealVector Q μ U polynomialBasisDegree p B n

/-- The paper defines the vector Wiener norm as the sum of coordinate norms.
The carrier's ambient product space uses the maximum; the comparison below
records the finite, n-independent conversion explicitly. -/
def coordinateWienerNorm {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (T : I → SymmetricReal d V) : ℝ := ∑ i, ‖T i‖

theorem coordinateWienerNorm_nonneg {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (T : I → SymmetricReal d V) : 0 ≤ coordinateWienerNorm T :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem coordinateWienerNorm_le {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (T : I → SymmetricReal d V) : coordinateWienerNorm T ≤ (Fintype.card I : ℝ) * ‖T‖ := by
  calc
    _ ≤ ∑ _i : I, ‖T‖ := Finset.sum_le_sum (fun i _ => norm_le_pi_norm T i)
    _ = _ := by simp

theorem paper_wiener_strong (Q : ℕ) (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ) :
    ∃ C ≥ 0, ∀ p B (n : ℕ), logarithmicThreshold p B (n + 1) ≤ 1 →
      coordinateWienerNorm (paperIdealVector Q μ U p B n) ≤
        C * (1 + Real.log (1 / logarithmicThreshold p B (n + 1))) ^ Q.choose 2 *
          ∑ j ∈ Finset.Icc 2 (4 * Q),
            (polynomialAmplitude p (n + 1) / logarithmicThreshold p B (n + 1)) ^ j := by
  obtain ⟨C, hC, hb⟩ := partB_wiener_strong Q μ U polynomialBasisDegree
  let M : ℝ := Fintype.card (MomentExponent (CoefficientExponent d Q) (4 * Q))
  have hM : 0 ≤ M := Nat.cast_nonneg _
  refine ⟨M * C, mul_nonneg hM hC, ?_⟩
  intro p B n ht
  have hn := (coordinateWienerNorm_le (paperIdealVector Q μ U p B n)).trans
    (mul_le_mul_of_nonneg_left (hb p B n ht) hM)
  simpa only [paperIdealVector, mul_assoc] using hn

theorem paper_wiener_rate (Q : ℕ) (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      coordinateWienerNorm (paperIdealVector Q μ U p B n) ≤
        C * logScale (n + 1) ^ ((Q.choose 2 : ℝ) - 2 * B) := by
  obtain ⟨C, hC, hb⟩ := partB_wiener_rate Q μ U polynomialBasisDegree p B hp hB
  let M : ℝ := Fintype.card (MomentExponent (CoefficientExponent d Q) (4 * Q))
  have hM : 0 ≤ M := Nat.cast_nonneg _
  refine ⟨M * C, mul_nonneg hM hC, ?_⟩
  filter_upwards [hb] with n hn
  have hh := (coordinateWienerNorm_le (paperIdealVector Q μ U p B n)).trans
    (mul_le_mul_of_nonneg_left hn hM)
  simpa only [paperIdealVector, mul_assoc] using hh

theorem paper_wiener_vanishes (Q : ℕ) (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (p B : ℝ) (hp : 0 < p) (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    Tendsto (fun n => coordinateWienerNorm (paperIdealVector Q μ U p B n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => coordinateWienerNorm_nonneg _) (fun _ => coordinateWienerNorm_le _)
  have h := (partB_wiener_vanishes Q μ U polynomialBasisDegree p B hp hB).const_mul
    (Fintype.card (MomentExponent (CoefficientExponent d Q) (4 * Q)) : ℝ)
  simpa only [paperIdealVector, mul_zero] using h

/-- The complete analytic conclusion of item 1, with exactly the canonical
coefficient space and moment vector. The finite-support law is strictly
positive and its moment right inverse is the separate item-2 input. There
is no supplied Wiener bound, limit, symmetry, or polarization assumption. -/
theorem paper_item_one (Q : ℕ) [NeZero Q]
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (p B : ℝ) (hp : 0 < p) (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B)
    (hμ : ∀ ω, 0 < μ.weight ω) (R : MomentRightInverse (monomialFeature (D := 4 * Q) U)) :
    (∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      coordinateWienerNorm (paperIdealVector Q μ U p B n) ≤ C * logScale (n + 1) ^ ((Q.choose 2 : ℝ) - 2 * B)) ∧
    Tendsto (fun n => coordinateWienerNorm (paperIdealVector Q μ U p B n)) atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, HasPositiveCarrier 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) (1 / 4))
      (multiplicationIncrement (paperIdealVector Q μ U p B n)) (monomialFeature U) μ) := by
  have hB0 : 0 ≤ B := by have := Nat.cast_nonneg (α := ℝ) (Q.choose 2); linarith
  exact ⟨paper_wiener_rate Q μ U p B hp hB0,
    paper_wiener_vanishes Q μ U p B hp hB,
    partB_analytic_positiveCarrier Q μ U polynomialBasisDegree p B hp hB hμ R⟩

end CausalLowerbound.PartB.ShellGeometry
