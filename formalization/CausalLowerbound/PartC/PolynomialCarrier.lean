import CausalLowerbound.PartC.ReflectedMomentPolarization
import CausalLowerbound.PartC.PairedSignCarrier

/-! The full polynomial polarization feeds the positive common-label
carrier. Its coefficients and atom reconstruction are constructed here;
the remaining analytic input is the concrete target operator. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Representative

open PartB

variable {d ι J I : Type*} [Fintype d] [Fintype ι] [Fintype J] [Fintype I]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

theorem naturalMomentTarget_bound
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ)
    (T : Array d ι J D →L[ℝ] (I → Array d ι J D))
    (δ : ℝ) (hT : ∀ a, ‖T a‖ ≤ δ * ‖a‖) (a : Array d ι J D) :
    ‖((naturalMomentCoefficients center hc θ).comp T) a‖ ≤
      (((Fintype.card I : ℝ) * polarizationBound ι θ) * δ) * ‖a‖ := by
  exact (naturalMomentCoefficients_bound center hc θ (T a)).trans
    ((mul_le_mul_of_nonneg_left (hT a)
      (mul_nonneg (Nat.cast_nonneg _) (polarizationBound_nonneg θ))).trans_eq (mul_assoc _ _ _).symm)

theorem reflectedMomentTarget_bound
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ)
    (T : Array d ι J D →L[ℝ] (I → Array d ι J D))
    (δ : ℝ) (hT : ∀ a, ‖T a‖ ≤ δ * ‖a‖) (a : Array d ι J D) :
    ‖((reflectedMomentCoefficients center hc θ).comp T) a‖ ≤
      (((Fintype.card I : ℝ) * polarizationBound ι θ) * δ) * ‖a‖ := by
  exact (reflectedMomentCoefficients_bound center hc θ (T a)).trans
    ((mul_le_mul_of_nonneg_left (hT a)
      (mul_nonneg (Nat.cast_nonneg _) (polarizationBound_nonneg θ))).trans_eq (mul_assoc _ _ _).symm)

def polynomialCarrierCoefficients
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ)
    (T : Array d ι J D →L[ℝ] (I → Array d ι J D))
    (δ : ℝ) (hT : ∀ a, ‖T a‖ ≤ δ * ‖a‖) :
    CarrierCoefficients (Array d ι J D) ((I → Walsh.Coefficients J) × (I → Walsh.Coefficients J))
      ((((Fintype.card I : ℝ) * polarizationBound ι θ) * δ) +
        (((Fintype.card I : ℝ) * polarizationBound ι θ) * δ)) :=
  pairedCarrierCoefficients ((naturalMomentCoefficients center hc θ).comp T)
    ((reflectedMomentCoefficients center hc θ).comp T) _ _
    (naturalMomentTarget_bound center hc θ T δ hT) (reflectedMomentTarget_bound center hc θ T δ hT)

variable {X Γ : Type*} [TopologicalSpace X] [CompactSpace X] [Fintype Γ]

theorem exists_polynomial_sign_carrier [Nonempty ι]
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (hθ : θ ≠ 0)
    (T : Array d ι J D →L[ℝ] (I → Array d ι J D))
    (δ : ℝ) (hδ : 0 ≤ δ) (hT : ∀ a, ‖T a‖ ≤ δ * ‖a‖)
    (x : X → Wiener.Torus (ι × d)) (hx : Continuous x)
    (z : (J → Bool) → ι → X → ℝ) (hz : ∀ ζ i, Continuous (z ζ i)) (hb : ∀ ζ i u, |z ζ i u| ≤ 1)
    (hflip : ∀ ζ i u, z (Walsh.flip ζ) i u = -z ζ i u)
    (hsym : ∀ a ζ i u (σ : Equiv.Perm ι), pointValue (Wiener.permuteSlots σ.symm (x u))
      (fun j => z ζ (σ.symm j) u) ζ (T a i) = pointValue (x u) (fun j => z ζ j u) ζ (T a i))
    (feature : I → Γ → ℝ) (μ : FiniteLaw Γ) (hμ : ∀ y, 0 < μ.weight y) (radius : ℝ)
    (realize : ∀ v : I → ℝ, (∀ i, |v i| ≤ radius) →
      ∃ ν : FiniteLaw Γ, (∀ y, 0 < ν.weight y) ∧
        ∀ i, ν.expect (feature i) = μ.expect (feature i) + v i)
    (K : ℝ) (hK : 0 < K) (hinv : K⁻¹ ≤ radius)
    (hsmall : K * ((1 + |θ|) ^ Fintype.card ι + 1) *
      (2 * (((Fintype.card I : ℝ) * polarizationBound ι θ) * δ)) ≤ 1 / 2)
    (hmass : 2 * K * (2 * (((Fintype.card I : ℝ) * polarizationBound ι θ) * δ)) < 1) :
    let L := ((Fintype.card I : ℝ) * polarizationBound ι θ) * δ
    let C := polynomialCarrierCoefficients center hc θ T δ hT
    let atom := pairedAtom reflection (naturalPolynomialAtom center θ)
    let ev := fun ζ => chartEvaluation x hx (z ζ) (hz ζ) (hb ζ) ζ
    ∃ (B : Array d ι J D) (H : DiscreteLaw ℕ) (kernel : (J → Bool) → ℕ → FiniteLaw Γ),
      C.update K unit atom B = B ∧ reflection B = B ∧
      ‖B - unit‖ ≤ 2 * (K * ((1 + |θ|) ^ Fintype.card ι + 1) * (L + L)) ∧ 0 < H.weight 0 ∧
      (∀ n, H.weight (n + 1) = K * ‖C.coeff B n‖) ∧
      (∀ n, H.weight (PairedSeries.flipLabel n + 1) = H.weight (n + 1)) ∧
      (∀ ζ, kernel ζ 0 = μ) ∧ (∀ ζ n y, 0 < (kernel ζ n).weight y) ∧
      (∀ ζ n, (∑ y, (H.joint (kernel ζ)).weight (n, y)) = H.weight n) ∧
      HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom unit atom n) B ∧
      (∀ ζ, HasSum (fun n => H.weight n • ev ζ (CarrierCoefficients.labeledAtom unit atom n)) (ev ζ B)) ∧
      ∀ ζ i, HasSum (fun n => (H.weight n *
        ((kernel ζ n).expect (feature i) - μ.expect (feature i))) •
        CarrierCoefficients.labeledAtom (ev ζ unit) (fun m => ev ζ (atom m)) n) (ev ζ (T B i)) := by
  apply exists_paired_sign_carrier
    ((naturalMomentCoefficients center hc θ).comp T) ((reflectedMomentCoefficients center hc θ).comp T)
    _ _ (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (polarizationBound_nonneg θ)) hδ)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (polarizationBound_nonneg θ)) hδ)
    (naturalMomentTarget_bound center hc θ T δ hT) (reflectedMomentTarget_bound center hc θ T δ hT)
    reflection reflection_involution (fun a => (reflection_norm a).le)
    unit (by rw [unit_norm]) reflection_unit (naturalPolynomialAtom center θ)
    _ (by positivity) (naturalPolynomialAtom_sub_unit_bound center hc θ)
    Walsh.evaluateCoordinate Walsh.evaluateCoordinate_bound
    (fun ζ => chartEvaluation x hx (z ζ) (hz ζ) (hb ζ) ζ)
    (fun a ζ i => chartEvaluation x hx (z ζ) (hz ζ) (hb ζ) ζ (T a i))
    _ _ feature μ hμ radius realize K hK hinv
    (by simpa only [two_mul] using hsmall) (by simpa only [two_mul] using hmass)
  · intro a ζ i
    exact naturalPolynomialCoefficients_chart_hasSum center hc θ hθ x hx
      (z ζ) (hz ζ) (hb ζ) ζ (T a i) (hsym a ζ i)
  · intro a ζ i
    exact reflectedMomentCoefficients_chart_hasSum center hc θ hθ x hx z hz hb hflip ζ (T a) i (hsym a ζ i)

end CausalLowerbound.PartC.Representative
