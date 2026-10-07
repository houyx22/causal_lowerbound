import CausalLowerbound.PartC.PolynomialChartReconstruction
import CausalLowerbound.PartC.VectorSeriesExtension
import CausalLowerbound.PartC.VectorSeriesStack

/-! The complete polynomial polarization on natural labels and finite
moment vectors. These are the actual coefficients used by the carrier. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC.Representative

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

local instance polynomialAtomEncodable : Encodable (PolynomialAtom d ι D) := Encodable.ofCountable _

def naturalPolynomialAtom (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (θ : ℝ) (n : ℕ) : Array d ι J D :=
  match Encodable.decode (α := PolynomialAtom d ι D) n with
  | some m => polynomialAtomTensor m.1 (center m.1) θ m.2
  | none => unit

theorem naturalPolynomialAtom_encode (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (θ : ℝ) (m : PolynomialAtom d ι D) :
    naturalPolynomialAtom center θ (Encodable.encode m) = polynomialAtomTensor m.1 (center m.1) θ m.2 := by
  simp only [naturalPolynomialAtom, Encodable.encodek]

theorem naturalPolynomialAtom_bound (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (n : ℕ) :
    ‖naturalPolynomialAtom center θ n‖ ≤ (1 + |θ|) ^ Fintype.card ι := by
  unfold naturalPolynomialAtom
  split
  · exact polynomialAtomTensor_norm _ _ (hc _) θ _
  · rw [unit_norm]
    exact one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg θ))

theorem naturalPolynomialAtom_sub_unit_bound (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (n : ℕ) :
    ‖naturalPolynomialAtom center θ n - unit‖ ≤ (1 + |θ|) ^ Fintype.card ι + 1 := by
  apply (norm_sub_le _ _).trans
  simpa only [unit_norm] using add_le_add_right (naturalPolynomialAtom_bound center hc θ n) 1

def naturalPolynomialCoefficients (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) : Array d ι J D →L[ℝ] VectorSeries.Family ℕ (Walsh.Coefficients J) :=
  (VectorSeries.extend (Encodable.encode : PolynomialAtom d ι D → ℕ) Encodable.encode_injective).comp
    (polarizationOperator center hc θ)

theorem naturalPolynomialCoefficients_bound (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (a : Array d ι J D) :
    ‖naturalPolynomialCoefficients center hc θ a‖ ≤ polarizationBound ι θ * ‖a‖ := by
  rw [naturalPolynomialCoefficients, ContinuousLinearMap.comp_apply, VectorSeries.extend_norm]
  exact polarizationOperator_bound center hc θ a

theorem polarizationBound_nonneg (θ : ℝ) : 0 ≤ polarizationBound ι θ := by
  unfold polarizationBound PartB.Polarization.stencilBound
  positivity

theorem naturalPolynomialCoefficients_chart_hasSum {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [Nonempty ι] (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (hθ : θ ≠ 0)
    (x : K → Wiener.Torus (ι × d)) (hx : Continuous x)
    (z : ι → K → ℝ) (hz : ∀ i, Continuous (z i)) (hb : ∀ i u, |z i u| ≤ 1)
    (ζ : J → Bool) (a : Array d ι J D)
    (hsym : ∀ u (σ : Equiv.Perm ι), pointValue (Wiener.permuteSlots σ.symm (x u))
      (fun i => z (σ.symm i) u) ζ a = pointValue (x u) (fun i => z i u) ζ a) :
    HasSum (fun n => Walsh.evaluate ζ (naturalPolynomialCoefficients center hc θ a n) •
      chartEvaluation x hx z hz hb ζ (naturalPolynomialAtom center θ n))
      (chartEvaluation x hx z hz hb ζ a) := by
  apply VectorSeries.extend_hasSum (Encodable.encode : PolynomialAtom d ι D → ℕ) Encodable.encode_injective
    (polarizationOperator center hc θ a)
    (fun n c => Walsh.evaluate ζ c • chartEvaluation x hx z hz hb ζ (naturalPolynomialAtom center θ n))
    (fun _ => by simp)
  simpa only [naturalPolynomialAtom_encode] using
    polarizationOperator_chart_hasSum center hc θ hθ x hx z hz hb ζ a hsym

variable {I : Type*} [Fintype I]

def naturalMomentCoefficients (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) :
    (I → Array d ι J D) →L[ℝ] VectorSeries.Family ℕ (I → Walsh.Coefficients J) :=
  VectorSeries.stack.comp (ContinuousLinearMap.pi (fun i =>
    (naturalPolynomialCoefficients center hc θ).comp (ContinuousLinearMap.proj i)))

@[simp] theorem naturalMomentCoefficients_apply (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (a : I → Array d ι J D) (n : ℕ) (i : I) :
    naturalMomentCoefficients center hc θ a n i = naturalPolynomialCoefficients center hc θ (a i) n := rfl

theorem naturalMomentCoefficients_bound (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (a : I → Array d ι J D) :
    ‖naturalMomentCoefficients center hc θ a‖ ≤
      ((Fintype.card I : ℝ) * polarizationBound ι θ) * ‖a‖ := by
  have hC := polarizationBound_nonneg (ι := ι) θ
  have hv : ‖fun i => naturalPolynomialCoefficients center hc θ (a i)‖ ≤ polarizationBound ι θ * ‖a‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg a))).mpr (fun i =>
      (naturalPolynomialCoefficients_bound center hc θ (a i)).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm a i) hC))
  exact (VectorSeries.stack_bound (fun i => naturalPolynomialCoefficients center hc θ (a i))).trans
    ((mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

end CausalLowerbound.PartC.Representative
