import CausalLowerbound.PartC.OutcomeChoiceTarget

/-! The degree-three target is a linear functional of the actual,
unaveraged shift polynomial. The occurrence filter removes exactly the
monomials whose degree exceeds three at some site. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
variable {Ω K V E d J : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype d] [DecidableEq d] [Fintype J] [DecidableEq J]

def cubicSiteDegree (e : V →₀ ℕ) (he : ∀ i, e i ≤ 3) : Degree V 3 :=
  fun i => ⟨e i, Nat.lt_succ_of_le (he i)⟩

def cubicSiteFunctional (w : Degree V 3 → ℝ) : MvPolynomial V ℝ →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun e : V →₀ ℕ => if he : ∀ i, e i ≤ 3 then w (cubicSiteDegree e he) else 0)

theorem cubicSiteFunctional_monomial (w : Degree V 3 → ℝ) (e : V →₀ ℕ) (c : ℝ) :
    cubicSiteFunctional w (MvPolynomial.monomial e c) =
      c * (if he : ∀ i, e i ≤ 3 then w (cubicSiteDegree e he) else 0) :=
  Finsupp.linearCombination_single ℝ c e

theorem cubicSiteFunctional_prod_X (w : Degree V 3 → ℝ) (sites : K → V) :
    cubicSiteFunctional w (∏ k, X (sites k)) =
      if he : ∀ i, siteOccurrenceExponent sites i ≤ 3 then
        w (cubicSiteDegree (siteOccurrenceExponent sites) he) else 0 := by
  have he : (∏ k, X (sites k) : MvPolynomial V ℝ) =
      MvPolynomial.monomial (siteOccurrenceExponent sites) 1 :=
    (MvPolynomial.monomial_sum_one Finset.univ (fun k => Finsupp.single (sites k) 1)).symm
  rw [he, cubicSiteFunctional_monomial, one_mul]

theorem cubicSiteFunctional_C (w : Degree V 3 → ℝ) (c : ℝ) :
    cubicSiteFunctional w (C c) = c * w (fun _ => 0) := by
  simpa only [Finsupp.zero_apply, Nat.zero_le, implies_true, dite_true, cubicSiteDegree] using
    cubicSiteFunctional_monomial w 0 c

theorem cubicSiteFunctional_shift (w : Degree V 3 → ℝ) (μ : FiniteLaw Ω)
    (U : Ω → K → ℝ) (c : K → V → ℝ) (amp : ℝ) :
    cubicSiteFunctional w (wordShiftPolynomial μ U c amp) =
      ∑ s : K → Option V, if hs : ∀ i, siteOccurrenceExponent (choiceSite s) i ≤ 3 then
        (shiftChoiceWeight μ U s * amp ^ choiceDegree s *
          ∏ k : ShiftPositions s, c k.val (choiceSite s k)) * w (outcomeChoiceDegree s hs) else 0 := by
  rw [wordShiftPolynomial_expansion, map_sum]
  simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul, cubicSiteFunctional_prod_X,
    cubicSiteDegree, outcomeChoiceDegree, mul_dite, mul_zero]
  rfl

def outcomePatternWeight (κ : V → ℝ) (v : Representative.Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (e : Degree V 3) : ℝ :=
  ∑ r : Row V J 3, Walsh.character r.2 ζ * (toContinuous (v r) (torusProjection u)).re *
    ∏ i, outcomeSlotFactor e κ z r.1 i

def outcomePolynomialFunctional (κ : V → ℝ) (v : Representative.Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) : MvPolynomial V ℝ →ₗ[ℝ] ℝ :=
  cubicSiteFunctional (outcomePatternWeight κ v u z ζ)

theorem outcomePatternWeight_zero (κ : V → ℝ) (v : Representative.Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) :
    outcomePatternWeight κ v u z ζ (fun _ => 0) = pointValue (torusProjection u) z ζ v := by
  unfold outcomePatternWeight pointValue rowWeight Representative.monomial
  simp only [outcomeSlotFactor, if_true]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem outcomePolynomialFunctional_C (κ : V → ℝ) (v : Representative.Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (c : ℝ) :
    outcomePolynomialFunctional κ v u z ζ (C c) = c * pointValue (torusProjection u) z ζ v := by
  rw [outcomePolynomialFunctional, cubicSiteFunctional_C, outcomePatternWeight_zero]

theorem outcomeChoiceValue_eq_polynomial (a b : E → V) (μ : FiniteLaw Ω)
    (U : Ω → K → ℝ) (ν : K → d × Bool →₀ ℕ) (amp τ : ℝ) (κ : V → ℝ)
    (v : Representative.Array d V J 3) (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) :
    outcomeChoiceValue a b μ U ν amp τ κ v u z ζ =
      graphTaper a b taperCutoff τ (graphDistance a b u) *
        outcomePolynomialFunctional κ v u z ζ
          (wordShiftPolynomial μ U (fun k i => lagrangeCoefficient a b i (ν k) u) amp) := by
  rw [outcomePolynomialFunctional, cubicSiteFunctional_shift, Finset.mul_sum]
  unfold outcomeChoiceValue
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : ∀ i, siteOccurrenceExponent (choiceSite s) i ≤ 3
  · simp only [dif_pos hs, shiftChoiceCoefficient, taperedLagrangeProduct, outcomePatternWeight]
    ring
  · simp only [dif_neg hs, mul_zero]

end CausalLowerbound.PartC
